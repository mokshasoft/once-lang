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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF where

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
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.CCC.Codegen.CallsLinked
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.ProgramImage
import qualified MAlonzo.Code.Once.CCC.Codegen.ProgramImageFacts
import qualified MAlonzo.Code.Once.CCC.Codegen.ShapeTable
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotSeg
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStackPtr
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStackSlot
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStoreWF
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.readLoc
d_readLoc_20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_20 ~v0 ~v1 ~v2 ~v3 = du_readLoc_20
du_readLoc_20 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_20
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.Frame
d_Frame_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> ()
d_Frame_30 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.CallPost
d_CallPost_34 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.FlatState
d_FlatState_36 a0 a1 a2 a3 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.FlinkView
d_FlinkView_40 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.do-branch
d_do'45'branch_56 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_56 ~v0 v1 ~v2 ~v3 = du_do'45'branch_56 v1
du_do'45'branch_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'branch_56 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_938 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.do-call
d_do'45'call_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_60 ~v0 v1 ~v2 ~v3 = du_do'45'call_60 v1
du_do'45'call_60 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call_60 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.do-call-at
d_do'45'call'45'at_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'at_62 ~v0 v1 ~v2 ~v3 = du_do'45'call'45'at_62 v1
du_do'45'call'45'at_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'call'45'at_62 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'at_1284 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.do-jump
d_do'45'jump_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_74 ~v0 ~v1 ~v2 ~v3 = du_do'45'jump_74
du_do'45'jump_74 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_74
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_922
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.entry-of?
d_entry'45'of'63'_96 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
d_entry'45'of'63'_96 ~v0 ~v1 ~v2 ~v3 = du_entry'45'of'63'_96
du_entry'45'of'63'_96 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
du_entry'45'of'63'_96
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_entry'45'of'63'_168
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.fetch
d_fetch_124 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
d_fetch_124 ~v0 ~v1 ~v2 ~v3 = du_fetch_124
du_fetch_124 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
du_fetch_124 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.find-fn
d_find'45'fn_140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Maybe Integer
d_find'45'fn_140 ~v0 v1 ~v2 ~v3 = du_find'45'fn_140 v1
du_find'45'fn_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Maybe Integer
du_find'45'fn_140 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.find-label
d_find'45'label_142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_142 ~v0 v1 ~v2 ~v3 = du_find'45'label_142 v1
du_find'45'label_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_142 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.find-thunk
d_find'45'thunk_148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_148 ~v0 v1 ~v2 ~v3 = du_find'45'thunk_148 v1
du_find'45'thunk_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_148 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.flat-exec-instr
d_flat'45'exec'45'instr_168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_168 ~v0 v1 ~v2 ~v3
  = du_flat'45'exec'45'instr_168 v1
du_flat'45'exec'45'instr_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ft-at
d_ft'45'at_202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'at_202 ~v0 v1 ~v2 ~v3 = du_ft'45'at_202 v1
du_ft'45'at_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'at_202 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'at_194 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ft-go
d_ft'45'go_208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'go_208 ~v0 v1 ~v2 ~v3 = du_ft'45'go_208 v1
du_ft'45'go_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'go_208 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_192 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ft-match
d_ft'45'match_216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'match_216 ~v0 v1 ~v2 ~v3 = du_ft'45'match_216 v1
du_ft'45'match_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
du_ft'45'match_216 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_196 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.FlatState.falloc
d_falloc_328 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_328 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.FlatState.fclosure
d_fclosure_330 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_330 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.FlatState.flink
d_flink_332 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_332 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.FlatState.floc
d_floc_334 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_floc_334 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.FlatState.fpc
d_fpc_336 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_336 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.FlatState.fret
d_fret_338 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_338 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.FlatWF
d_FlatWF_356 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatWF_356 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.sv-below
d_sv'45'below_404 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_404 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ir-stack-budget
d_ir'45'stack'45'budget_590 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_590 v0 ~v1 ~v2 ~v3
  = du_ir'45'stack'45'budget_590 v0
du_ir'45'stack'45'budget_590 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'stack'45'budget_590 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_866
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.StackPtrOK
d_StackPtrOK_640 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_StackPtrOK_640 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.StackPtrWF
d_StackPtrWF_644 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_StackPtrWF_644 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.PtrB
d_PtrB_740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_PtrB_740 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.PtrBoundsWF
d_PtrBoundsWF_744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_PtrBoundsWF_744 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.AllocMinI
d_AllocMinI_902 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> ()
d_AllocMinI_902 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.Meets
d_Meets_966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Meets_966 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.Emitted
d_Emitted_1260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> ()
d_Emitted_1260 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.EntryLike
d_EntryLike_1262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_EntryLike_1262 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.Reachable
d_Reachable_1266 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.RunAt
d_RunAt_1268 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.RunAt.run-emit
d_run'45'emit_1302 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_1302 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.RunAt.run-ir
d_run'45'ir_1304 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_1304 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.RunAt.run-linked
d_run'45'linked_1306 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'linked_1306 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_444
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.RunAt.run-reach
d_run'45'reach_1308 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364
d_run'45'reach_1308 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.RunAt.run-tbl
d_run'45'tbl_1310 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_run'45'tbl_1310 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.fns-calls
d_fns'45'calls_1322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fns'45'calls_1322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_fns'45'calls_1322 v6 v7 v8
du_fns'45'calls_1322 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fns'45'calls_1322 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236
                             (coe
                                MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26
                                (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3)))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_896
                                (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3))
                                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                                (coe v0)
                                (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3)))))
                       (let v9
                              = MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3) in
                        coe
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_924
                             (coe v9)
                             (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                             (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                             (coe v0)
                             (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3)))))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.CallsLinked.du_ir'45'to'45'trace'45'lab'45'calls_938
                          (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3))
                          (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                          (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                          (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3))
                          (coe v0) (coe v7)))
                    (coe
                       du_fns'45'calls_1322
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                          (coe v3))
                       (coe v4) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.image-calls
d_image'45'calls_1346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_image'45'calls_1346 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_image'45'calls_1346 v0 v5 v6 v7
du_image'45'calls_1346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_image'45'calls_1346 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_link'45'top_2376
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_top'45'done_30
                      (coe v0)
                      (coe
                         MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
                         (coe v2)))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_842 v0
                      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v2))
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.CallsLinked.du_ir'45'to'45'trace'45'top'45'calls_954
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2) (coe v4))
                (coe
                   du_fns'45'calls_1322
                   (coe
                      addInt (coe (1 :: Integer))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_934
                         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
                         (coe v2)))
                   (coe v1) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.linked-any
d_linked'45'any_1366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_linked'45'any_1366 v0 v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_linked'45'any_1366 v0 v1 v2 v4 v5 v6 v7 v8
du_linked'45'any_1366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_linked'45'any_1366 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v3 of
      (:) v8 v9
        -> coe
             du_go_1392 (coe v0) (coe v1) (coe v2) (coe v9) (coe v4) (coe v5)
             (coe v6)
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__116
                (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v8))
                (coe v4))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200
                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v8))
                (coe v5))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200
                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v8))
                (coe v6))
             (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_1392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_go_1392 v0 v1 v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11 v12 v13
  = du_go_1392 v0 v1 v2 v5 v6 v7 v8 v10 v11 v12 v13
du_go_1392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_go_1392 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
        -> if coe v11
             then case coe v12 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                      -> case coe v8 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                             -> if coe v14
                                  then coe
                                         seq (coe v15)
                                         (case coe v9 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                              -> if coe v16
                                                   then coe
                                                          seq (coe v17)
                                                          (coe
                                                             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                             v13)
                                                   else coe
                                                          seq (coe v17)
                                                          (coe
                                                             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                             (coe
                                                                du_linked'45'any_1366 (coe v0)
                                                                (coe v1) (coe v2) (coe v3) (coe v4)
                                                                (coe v5) (coe v6) (coe v10)))
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  else coe
                                         seq (coe v15)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                            (coe
                                               du_linked'45'any_1366 (coe v0) (coe v1) (coe v2)
                                               (coe v3) (coe v4) (coe v5) (coe v6) (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v12)
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                       (coe
                          du_linked'45'any_1366 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v5) (coe v6) (coe v10)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.entries-in
d_entries'45'in_1412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_entries'45'in_1412 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7
  = du_entries'45'in_1412 v4 v5 v7
du_entries'45'in_1412 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_entries'45'in_1412 v0 v1 v2
  = case coe v1 of
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_'43''43''8314''737'_844
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'image_8 (coe v0)
                       (coe v3))
                    (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_'43''43''8314''691'_854
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'image_8 (coe v0)
                       (coe v3))
                    (coe
                       du_entries'45'in_1412
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                          (coe v3))
                       (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.≡ᵇᴱ-refl
d_'8801''7495''7473''45'refl_1438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''7473''45'refl_1438 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.ft-at-complete
d_ft'45'at'45'complete_1466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'at'45'complete_1466 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8
  = du_ft'45'at'45'complete_1466 v4 v6 v7 v8
du_ft'45'at'45'complete_1466 ::
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'at'45'complete_1466 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_match_1494 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7473'__276 (coe v4)
                (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe v3 (addInt (coe (1 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.match
d_match_1494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_match_1494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_match_1494 v7 v8 v9
du_match_1494 ::
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_match_1494 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) erased
      else coe v1 (addInt (coe (1 :: Integer)) (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.ft-go-complete
d_ft'45'go'45'complete_1506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'complete_1506 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_ft'45'go'45'complete_1506 v4 v5 v6 v7
du_ft'45'go'45'complete_1506 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'complete_1506 v0 v1 v2 v3
  = case coe v0 of
      (:) v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v8
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v8
               -> coe
                    du_ft'45'at'45'complete_1466
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_entry'45'of'63'_168 (coe v4))
                    (coe v1) (coe v2)
                    (coe
                       (\ v9 ->
                          coe
                            du_ft'45'go'45'complete_1506 (coe v5) (coe v1) (coe v9) (coe v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.emitted-call-fn-resolves
d_emitted'45'call'45'fn'45'resolves_1542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_emitted'45'call'45'fn'45'resolves_1542 v0 v1 v2 ~v3 v4 v5 v6 v7
                                         ~v8
  = du_emitted'45'call'45'fn'45'resolves_1542 v0 v1 v2 v4 v5 v6 v7
du_emitted'45'call'45'fn'45'resolves_1542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_emitted'45'call'45'fn'45'resolves_1542 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_ft'45'go'45'complete_1506 (coe v3)
      (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v5))
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_'43''43''8314''691'_854
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_866
                     (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                     (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                     (coe
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
                        (coe v6)))))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_link'45'top_2376
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_top'45'done_30
                  (coe v0)
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
                     (coe
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
                        (coe v6))
                     (coe
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
                        (coe v6))))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_842 v0
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
                     (coe v6)))))
         (coe
            du_entries'45'in_1412
            (coe
               addInt (coe (1 :: Integer))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_934
                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
                  (coe
                     MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
                     (coe v6))))
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
               (coe v6))
            (coe
               du_linked'45'any_1366 (coe v0) (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
                  (coe v6))
               (coe v5)
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe du_ok_1558 (coe v0) (coe v3) (coe v4) (coe v6)))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe du_ok_1558 (coe v0) (coe v3) (coe v4) (coe v6))))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe du_ok_1558 (coe v0) (coe v3) (coe v4) (coe v6)))))))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ok
d_ok_1558 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ok_1558 v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8 = du_ok_1558 v0 v4 v5 v7
du_ok_1558 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ok_1558 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_4132 (coe v1)
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v2))
      (coe
         du_image'45'calls_1346 (coe v0)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
            (coe v3))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
            (coe v3))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_444
            (coe v3)))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.call-site-shape
d_call'45'site'45'shape_1572
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatCore.RunWF.call-site-shape"
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.ret-site-owes
d_ret'45'site'45'owes_1584
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatCore.RunWF.ret-site-owes"
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.emitted-thunk-guarded
d_emitted'45'thunk'45'guarded_1602
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatCore.RunWF.emitted-thunk-guarded"
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.emitted-code-addr-has-body
d_emitted'45'code'45'addr'45'has'45'body_1614
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatCore.RunWF.emitted-code-addr-has-body"
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.ret-budget-matches
d_ret'45'budget'45'matches_1622
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatCore.RunWF.ret-budget-matches"
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.emitted-shape-check
d_emitted'45'shape'45'check_1630
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatCore.RunWF.emitted-shape-check"
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-meets
d_run'45'meets_1638
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-meets"
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.frame-op-absurd
d_frame'45'op'45'absurd_1648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_frame'45'op'45'absurd_1648 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8
  = du_frame'45'op'45'absurd_1648 v0 v5 v7
du_frame'45'op'45'absurd_1648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_frame'45'op'45'absurd_1648 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_4132
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_program'45'image_42
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v3)
                          (coe v5)))
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ProgramImageFacts.d_image'45'frame'45'free_76
                       (coe v0) (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.start-at-zero
d_start'45'at'45'zero_1666 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_start'45'at'45'zero_1666 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.fetch-zero
d_fetch'45'zero_1688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'zero_1688 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.fetch≡lookup
d_fetch'8801'lookup_1698 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'8801'lookup_1698 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.emitted-slot-below-budget
d_emitted'45'slot'45'below'45'budget_1720 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_emitted'45'slot'45'below'45'budget_1720 v0 ~v1 ~v2 ~v3 v4 v5 v6
                                          ~v7 v8 ~v9 ~v10
  = du_emitted'45'slot'45'below'45'budget_1720 v0 v4 v5 v6 v8
du_emitted'45'slot'45'below'45'budget_1720 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_emitted'45'slot'45'below'45'budget_1720 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.d_below_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45'at_980
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_program'45'image_42
            (coe v0)
            (coe
               MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
               (coe v2)))
         (coe v3)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ProgramImageFacts.d_image'45'slots_152
            (coe v0) (coe v1) (coe v2)))
      v4 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.ff→seg-id
d_ff'8594'seg'45'id_1738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ff'8594'seg'45'id_1738 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.call-seg-id
d_call'45'seg'45'id_1740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_call'45'seg'45'id_1740 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.RetMatch
d_RetMatch_1746 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_RetMatch_1746
  = C_rm'45''91''93'_1752 |
    C_rm'45''8759'_1768 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                        T_RetMatch_1746
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.SegCur
d_SegCur_1770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_SegCur_1770 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.SegWF
d_SegWF_1788 a0 a1 a2 a3 a4 a5 a6 = ()
data T_SegWF_1788
  = C_mkSegWF_1828 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
                   T_RetMatch_1746
                   (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
                    Integer ->
                    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.SegWF.seg-cur
d_seg'45'cur_1812 ::
  T_SegWF_1788 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_seg'45'cur_1812 v0
  = case coe v0 of
      C_mkSegWF_1828 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.SegWF.seg-stack
d_seg'45'stack_1814 :: T_SegWF_1788 -> T_RetMatch_1746
d_seg'45'stack_1814 v0
  = case coe v0 of
      C_mkSegWF_1828 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.SegWF.seg-entry
d_seg'45'entry_1826 ::
  T_SegWF_1788 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_seg'45'entry_1826 v0
  = case coe v0 of
      C_mkSegWF_1828 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.dj-aux
d_dj'45'aux_1836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_dj'45'aux_1836 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_dj'45'aux_1836 v4
du_dj'45'aux_1836 ::
  Maybe Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_dj'45'aux_1836 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.db-aux
d_db'45'aux_1854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_db'45'aux_1854 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7
  = du_db'45'aux_1854 v1 v4 v5 v6
du_db'45'aux_1854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_db'45'aux_1854 v0 v1 v2 v3
  = if coe v1
      then coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                du_dj'45'aux_1836
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                   (coe v3) (coe v2)))
      else coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.NotJmpI
d_NotJmpI_1868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> ()
d_NotJmpI_1868 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.JumpPost
d_JumpPost_1878 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_JumpPost_1878
  = C_jp'45'suc_1888 AgdaAny | C_jp'45'halt_1890 |
    C_jp'45'to_1894 Integer
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.PcView
d_PcView_1898 a0 a1 a2 a3 a4 = ()
data T_PcView_1898
  = C_pv'45'suc_1906 AgdaAny AgdaAny |
    C_pv'45'jump_1914 AgdaAny MAlonzo.Code.Once.CCC.Label.T_LabelId_6
                      ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                       T_JumpPost_1878) |
    C_pv'45'thunk_1920 MAlonzo.Code.Once.CCC.Label.T_EntryId_22
                       Integer |
    C_pv'45'ret_1924 Integer | C_pv'45'start_1928 Integer |
    C_pv'45'call_1930 |
    C_pv'45'call'45'fn_1934 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.pcView
d_pcView_1938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  AgdaAny -> T_PcView_1898
d_pcView_1938 ~v0 v1 ~v2 ~v3 v4 ~v5 = du_pcView_1938 v1 v4
du_pcView_1938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  T_PcView_1898
du_pcView_1938 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2276 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282
        -> coe C_pv'45'call_1930
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2284 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2286 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2288 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2290 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296 v2 v3 v4
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302 v2 v3 v4
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316 v2
        -> coe
             C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v2
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v3
               -> coe
                    C_pv'45'suc_1906 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 v3
               -> coe
                    C_pv'45'jump_1914 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v3
                    (\ v4 v5 -> coe du_go_1956 (coe v0) (coe v3) v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232 v3
               -> coe
                    C_pv'45'jump_1914 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v3
                    (coe du_go_1988 (coe v0) (coe v3))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v3
               -> coe
                    C_pv'45'jump_1914 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v3
                    (coe du_go_2020 (coe v0) (coe v3))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v3 v4
               -> coe C_pv'45'thunk_1920 v3 v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v3
               -> coe C_pv'45'ret_1924 v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240 v3
               -> coe C_pv'45'call'45'fn_1934 v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v3
               -> coe C_pv'45'start_1928 v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_1956 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_JumpPost_1878
d_go_1956 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 ~v7 = du_go_1956 v1 v4 v6
du_go_1956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  T_JumpPost_1878
du_go_1956 v0 v1 v2
  = coe
      du_mk_1968
      (coe
         du_dj'45'aux_1836
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
            (coe v2) (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.mk
d_mk_1968 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1878
d_mk_1968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_mk_1968 v8
du_mk_1968 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1878
du_mk_1968 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_jp'45'halt_1890
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe seq (coe v3) (coe C_jp'45'to_1894 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_1988 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_JumpPost_1878
d_go_1988 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 = du_go_1988 v1 v4 v6 v7
du_go_1988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_JumpPost_1878
du_go_1988 v0 v1 v2 v3
  = coe
      du_mk_1998
      (coe
         du_db'45'aux_1854 (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
                  (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)))
         (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.mk
d_mk_1998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1878
d_mk_1998 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_mk_1998 v8
du_mk_1998 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1878
du_mk_1998 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_jp'45'suc_1888 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
               -> coe C_jp'45'halt_1890
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                      -> coe seq (coe v4) (coe C_jp'45'to_1894 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_2020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_JumpPost_1878
d_go_2020 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 = du_go_2020 v1 v4 v6 v7
du_go_2020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_JumpPost_1878
du_go_2020 v0 v1 v2 v3
  = coe
      du_mk_2030
      (coe
         du_db'45'aux_1854 (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))))
         (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.mk
d_mk_2030 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1878
d_mk_2030 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_mk_2030 v8
du_mk_2030 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_JumpPost_1878
du_mk_2030 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_jp'45'suc_1888 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
               -> coe C_jp'45'halt_1890
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                      -> coe seq (coe v4) (coe C_jp'45'to_1894 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-seg-wf
d_run'45'seg'45'wf_2140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  T_SegWF_1788
d_run'45'seg'45'wf_2140 v0 v1 v2 ~v3 v4 v5 v6
  = du_run'45'seg'45'wf_2140 v0 v1 v2 v4 v5 v6
du_run'45'seg'45'wf_2140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  T_SegWF_1788
du_run'45'seg'45'wf_2140 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_448 v6 v7 v9 v10
        -> coe
             du_go_2216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe v7) (coe v9) (coe v10) (coe v10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.B₀
d_B'8320'_2160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegState_144
d_B'8320'_2160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_B'8320'_2160
du_B'8320'_2160 ::
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegState_144
du_B'8320'_2160
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C_mkSeg_154
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.0≢suc
d_0'8802'suc_2164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_0'8802'suc_2164 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.suc-inj
d_suc'45'inj_2170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'inj_2170 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.just-injI
d_just'45'injI_2176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injI_2176 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.Guard
d_Guard_2178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer -> ()
d_Guard_2178 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.guard
d_guard_2194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_guard_2194 v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10 v11 v12 v13
             ~v14
  = du_guard_2194 v0 v1 v2 v6 v7 v11 v12 v13
du_guard_2194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_guard_2194 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      d_emitted'45'thunk'45'guarded_1602 v0 v1 v2 erased v3 v4 v5 v6 v7
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_2216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  T_SegWF_1788
d_go_2216 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 v12
  = du_go_2216 v0 v1 v2 v4 v5 v6 v7 v9 v10 v12
du_go_2216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  T_SegWF_1788
du_go_2216 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'start_372 v11
        -> coe
             C_mkSegWF_1828
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
             (coe C_rm'45''91''93'_1752)
             (coe
                (\ v13 v14 v15 ->
                   coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'step_378 v10 v11 v12
        -> coe
             du_step_2372 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v11) (coe v12)
             (coe du_pcView_1938 (coe v1) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.em
d_em_2248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_em_2248 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11 v12 ~v13
          ~v14 ~v15
  = du_em_2248 v0 v6 v7 v8 v12
du_em_2248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_em_2248 v0 v1 v2 v3 v4
  = coe
      du_frame'45'op'45'absurd_1648 (coe v0) (coe v4)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.ih
d_ih_2250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SegWF_1788
d_ih_2250 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 v12 v13 ~v14
          ~v15
  = du_ih_2250 v0 v1 v2 v4 v5 v6 v7 v9 v10 v12 v13
du_ih_2250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  T_SegWF_1788
du_ih_2250 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_go_2216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v10)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.lk
d_lk_2252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lk_2252 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.seg-suc
d_seg'45'suc_2254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'suc_2254 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.ih-eq
d_ih'45'eq_2260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'45'eq_2260 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.go-eq
d_go'45'eq_2268 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go'45'eq_2268 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.ff-not-thunk
d_ff'45'not'45'thunk_2282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ff'45'not'45'thunk_2282 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.no-fallthrough
d_no'45'fallthrough_2304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'fallthrough_2304 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.clash
d_clash_2328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_clash_2328 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.ff-not-ret
d_ff'45'not'45'ret_2352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ff'45'not'45'ret_2352 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.nj-eq
d_nj'45'eq_2364 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nj'45'eq_2364 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.step
d_step_2372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_PcView_1898 -> T_SegWF_1788
d_step_2372 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 v12 v13 ~v14
            ~v15 v16
  = du_step_2372 v0 v1 v2 v4 v5 v6 v7 v9 v10 v12 v13 v16
du_step_2372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  T_PcView_1898 -> T_SegWF_1788
du_step_2372 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      C_pv'45'suc_1906 v12 v13
        -> coe
             C_mkSegWF_1828
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
             (coe
                d_seg'45'stack_1814
                (coe
                   du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)))
             (coe
                (\ v15 v16 v17 ->
                   coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      C_pv'45'jump_1914 v12 v13 v15
        -> coe
             C_mkSegWF_1828
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
             (coe
                d_seg'45'stack_1814
                (coe
                   du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)))
             (coe
                (\ v16 v17 v18 ->
                   coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      C_pv'45'thunk_1920 v12 v13
        -> coe
             C_mkSegWF_1828
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
             (coe
                d_seg'45'stack_1814
                (coe
                   du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)))
             (coe
                (\ v15 v16 v17 ->
                   coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      C_pv'45'ret_1924 v12
        -> coe
             du_ret'45'step_2614 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      C_pv'45'start_1928 v12
        -> coe
             C_mkSegWF_1828
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
             (coe
                d_seg'45'stack_1814
                (coe
                   du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)))
             (coe
                (\ v14 v15 v16 ->
                   coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      C_pv'45'call_1930
        -> coe
             du_call'45'go_2698 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      C_pv'45'call'45'fn_1934 v12
        -> coe
             du_callfn'45'go_2762 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.same
d_same_2384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackSlot.T_SameFrames_524
d_same_2384 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.stable
d_stable_2386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stable_2386 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.same
d_same_2410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   T_JumpPost_1878) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackSlot.T_SameFrames_524
d_same_2410 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.lkm
d_lkm_2412 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   T_JumpPost_1878) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lkm_2412 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.jgo
d_jgo_2414 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   T_JumpPost_1878) ->
  T_JumpPost_1878 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_jgo_2414 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.ego
d_ego_2444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   T_JumpPost_1878) ->
  T_JumpPost_1878 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ego_2444 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.i≡thunk
d_i'8801'thunk_2470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   T_JumpPost_1878) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8801'thunk_2470 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.no-once
d_no'45'once_2476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   T_JumpPost_1878) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_no'45'once_2476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                  ~v25
  = du_no'45'once_2476
du_no'45'once_2476 :: AgdaAny
du_no'45'once_2476 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.clash
d_clash_2496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   T_JumpPost_1878) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_clash_2496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
             ~v26 ~v27
  = du_clash_2496
du_clash_2496 :: AgdaAny
du_clash_2496 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.entry-not-ret
d_entry'45'not'45'ret_2518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_entry'45'not'45'ret_2518 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.entry-not-jmp
d_entry'45'not'45'jmp_2524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_entry'45'not'45'jmp_2524 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.pc-eq
d_pc'45'eq_2528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'eq_2528 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.step-eq
d_step'45'eq_2530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_2530 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.start-not-ret
d_start'45'not'45'ret_2558 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'45'not'45'ret_2558 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.start-not-jmp
d_start'45'not'45'jmp_2564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'45'not'45'jmp_2564 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.pc-eq′
d_pc'45'eq'8242'_2568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'eq'8242'_2568 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.step-eq′
d_step'45'eq'8242'_2570 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq'8242'_2570 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.ret-clash
d_ret'45'clash_2600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ret'45'clash_2600 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.go-c
d_go'45'c_2612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_go'45'c_2612 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.ret-step
d_ret'45'step_2614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SegWF_1788
d_ret'45'step_2614 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 v12 v13
                   ~v14 ~v15 ~v16 ~v17 ~v18
  = du_ret'45'step_2614 v0 v1 v2 v4 v5 v6 v7 v9 v10 v12 v13
du_ret'45'step_2614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  T_SegWF_1788
du_ret'45'step_2614 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_go'45'rm_2624
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v9))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v9)))
      (coe
         d_seg'45'stack_1814
         (coe
            du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.go-rm
d_go'45'rm_2624 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RetMatch_1746 -> T_SegWF_1788
d_go'45'rm_2624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21
  = du_go'45'rm_2624 v17 v18 v21
du_go'45'rm_2624 ::
  [Integer] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_RetMatch_1746 -> T_SegWF_1788
du_go'45'rm_2624 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   C_mkSegWF_1828
                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
                   (coe C_rm'45''91''93'_1752)
                   (coe
                      (\ v3 v4 v5 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))))
      (:) v3 v4
        -> case coe v1 of
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v2 of
                       C_rm'45''8759'_1768 v13 v14
                         -> coe
                              C_mkSegWF_1828
                              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased) (coe v14)
                              (coe
                                 (\ v15 v16 v17 ->
                                    coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.call-go
d_call'45'go_2698 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SegWF_1788
d_call'45'go_2698 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 v12 v13
                  ~v14 ~v15 ~v16 ~v17
  = du_call'45'go_2698 v0 v1 v2 v4 v5 v6 v7 v9 v10 v12 v13
du_call'45'go_2698 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  T_SegWF_1788
du_call'45'go_2698 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_cgo_2716 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) erased
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1368 (coe v1)
         (coe v3) (coe v9))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.call-clash
d_call'45'clash_2708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_call'45'clash_2708 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.beq
d_beq_2710 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_beq_2710 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.cgo
d_cgo_2716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350 -> T_SegWF_1788
d_cgo_2716 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 v11 v12 v13 ~v14
           ~v15 v16
  = du_cgo_2716 v0 v1 v2 v4 v5 v6 v7 v9 v10 v11 v12 v13 v16
du_cgo_2716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350 -> T_SegWF_1788
du_cgo_2716 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.Flat.C_cp'45'halt_1356
        -> coe
             C_mkSegWF_1828
             (coe
                d_seg'45'cur_1812
                (coe
                   du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)))
             (coe
                d_seg'45'stack_1814
                (coe
                   du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)))
             (coe
                (\ v14 v15 v16 ->
                   coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      MAlonzo.Code.Once.CCC.Machine.Flat.C_cp'45'enter_1362 v13 v14
        -> coe
             C_mkSegWF_1828
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v13))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe du_landing_2742 (coe v1) (coe v3) (coe v14) (coe v13)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe du_landing_2742 (coe v1) (coe v3) (coe v14) (coe v13)))
                         erased))))
             (coe
                C_rm'45''8759'_1768
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v9))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                (d_seg'45'stack_1814
                   (coe
                      du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10))))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v9)))
                           erased)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v9)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v9))
                              erased)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._._.landing
d_landing_2742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_landing_2742 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19
  = du_landing_2742 v1 v4 v6 v18
du_landing_2742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_landing_2742 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_find'45'entry'45'sound_882
      (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v3)) (coe v2)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.callfn-go
d_callfn'45'go_2762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SegWF_1788
d_callfn'45'go_2762 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 v12
                    v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_callfn'45'go_2762 v0 v1 v2 v4 v5 v6 v7 v9 v10 v12 v13 v16
du_callfn'45'go_2762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> T_SegWF_1788
du_callfn'45'go_2762 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_cfgo_2782 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) erased
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240 (coe v1)
         (coe v3) (coe v11))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.cf-clash
d_cf'45'clash_2772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cf'45'clash_2772 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.beq
d_beq_2774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_beq_2774 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.cfgo
d_cfgo_2782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_SegWF_1788
d_cfgo_2782 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 v11 v12 ~v13 v14
            v15 ~v16 v17 ~v18
  = du_cfgo_2782 v0 v1 v2 v4 v5 v6 v7 v9 v10 v11 v12 v14 v15 v17
du_cfgo_2782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer -> T_SegWF_1788
du_cfgo_2782 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             C_mkSegWF_1828
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v11))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe du_landing_2804 (coe v1) (coe v3) (coe v11) (coe v14)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe du_landing_2804 (coe v1) (coe v3) (coe v11) (coe v14)))
                         erased))))
             (coe
                C_rm'45''8759'_1768
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v9))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240
                               (coe v11)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                (d_seg'45'stack_1814
                   (coe
                      du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10))))
             (coe
                (\ v15 v16 v17 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v9)))
                           erased)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v9)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v9))
                              erased)))))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_mkSegWF_1828
             (coe
                d_seg'45'cur_1812
                (coe
                   du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)))
             (coe
                d_seg'45'stack_1814
                (coe
                   du_ih_2250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)))
             (coe
                (\ v14 v15 v16 ->
                   coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._._.landing
d_landing_2804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_landing_2804 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_landing_2804 v1 v4 v5 v6
du_landing_2804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_landing_2804 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_find'45'entry'45'sound_882
      (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v2)) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.entry-empty
d_entry'45'empty_2824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'45'empty_2824 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.entry-link
d_entry'45'link_2848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'link_2848 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9
  = du_entry'45'link_2848 v0 v1 v2 v4 v5 v6 v7 v8
du_entry'45'link_2848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'link_2848 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            d_seg'45'entry_1826
            (coe
               du_run'45'seg'45'wf_2140 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v4) (coe v7))
            v5 v6 erased))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.entry-ret
d_entry'45'ret_2874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'ret_2874 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9
  = du_entry'45'ret_2874 v0 v1 v2 v4 v5 v6 v7 v8
du_entry'45'ret_2874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'ret_2874 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            d_seg'45'entry_1826
            (coe
               du_run'45'seg'45'wf_2140 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v4) (coe v7))
            v5 v6 erased))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.thunk-entry-empty
d_thunk'45'entry'45'empty_2896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thunk'45'entry'45'empty_2896 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.thunk-entry-link
d_thunk'45'entry'45'link_2920 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'entry'45'link_2920 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9
  = du_thunk'45'entry'45'link_2920 v0 v1 v2 v4 v5 v6 v7 v8
du_thunk'45'entry'45'link_2920 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'entry'45'link_2920 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            d_seg'45'entry_1826
            (coe
               du_run'45'seg'45'wf_2140 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v4) (coe v7))
            (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v5)) v6
            erased))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.thunk-entry-ret
d_thunk'45'entry'45'ret_2946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'entry'45'ret_2946 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9
  = du_thunk'45'entry'45'ret_2946 v0 v1 v2 v4 v5 v6 v7 v8
du_thunk'45'entry'45'ret_2946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'entry'45'ret_2946 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            d_seg'45'entry_1826
            (coe
               du_run'45'seg'45'wf_2140 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v4) (coe v7))
            (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v5)) v6
            erased))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.stack-ptr-step
d_stack'45'ptr'45'step_2966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_534 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_534
d_stack'45'ptr'45'step_2966 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 v10
  = du_stack'45'ptr'45'step_2966 v1 v4 v5 v6 v10
du_stack'45'ptr'45'step_2966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_534 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_534
du_stack'45'ptr'45'step_2966 v0 v1 v2 v3 v4
  = coe
      seq (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_flat'45'stack'45'ptr_1888
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.entry-stack-ptr
d_entry'45'stack'45'ptr_3374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_534
d_entry'45'stack'45'ptr_3374 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_entry'45'stack'45'ptr_3374 v4 v5
du_entry'45'stack'45'ptr_3374 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_534
du_entry'45'stack'45'ptr_3374 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> case coe v15 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                         -> coe
                                                              seq (coe v17)
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.C_mkStackPtrWF_566
                                                                 (coe
                                                                    (\ v18 ->
                                                                       coe
                                                                         du_go_3392
                                                                         (coe
                                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                                                                            (coe
                                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
                                                                               (coe
                                                                                  MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                                                                  (coe v0)))
                                                                            (coe v18))))
                                                                 (coe
                                                                    (\ v18 ->
                                                                       coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                 (coe
                                                                    (\ v18 v19 ->
                                                                       coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_3392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_3392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 ~v17
  = du_go_3392 v16
du_go_3392 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_go_3392 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v1
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.entry-ptr-bounds
d_entry'45'ptr'45'bounds_3442 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_574
d_entry'45'ptr'45'bounds_3442 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_entry'45'ptr'45'bounds_3442 v4 v5
du_entry'45'ptr'45'bounds_3442 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_574
du_entry'45'ptr'45'bounds_3442 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> case coe v15 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                         -> coe
                                                              seq (coe v17)
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.C_mkPtrBounds_608
                                                                 (coe
                                                                    (\ v18 ->
                                                                       coe
                                                                         du_go_3460
                                                                         (coe
                                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                                                                            (coe
                                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
                                                                               (coe
                                                                                  MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                                                                  (coe v0)))
                                                                            (coe v18))))
                                                                 (coe
                                                                    (\ v18 ->
                                                                       coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                 (coe
                                                                    (\ v18 v19 ->
                                                                       coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_3460 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_3460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 ~v17
  = du_go_3460 v16
du_go_3460 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_go_3460 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v1
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.entry-flat-wf
d_entry'45'flat'45'wf_3510 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736
d_entry'45'flat'45'wf_3510 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_entry'45'flat'45'wf_3510 v4 v5
du_entry'45'flat'45'wf_3510 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736
du_entry'45'flat'45'wf_3510 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> case coe v15 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                         -> coe
                                                              seq (coe v17)
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.C_constructor_778
                                                                 (\ v18 ->
                                                                    coe
                                                                      du_go_3528
                                                                      (coe
                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                                                                         (coe
                                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
                                                                            (coe
                                                                               MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                                                               (coe v0)))
                                                                         (coe v18)))
                                                                 (\ v18 ->
                                                                    coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                 (\ v18 v19 ->
                                                                    coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_3528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_go_3528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 ~v17
  = du_go_3528 v16
du_go_3528 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_go_3528 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v1
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-step-pc-pos
d_run'45'step'45'pc'45'pos_3586 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_run'45'step'45'pc'45'pos_3586 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.z≢s
d_z'8802's_3604 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_z'8802's_3604 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.jI
d_jI_3610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_jI_3610 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.at-zero
d_at'45'zero_3616 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'zero_3616 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.unmoved
d_unmoved_3626 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_unmoved_3626 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.lab≢start
d_lab'8802'start_3638 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_lab'8802'start_3638 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ent≢start
d_ent'8802'start_3646 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ent'8802'start_3646 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.step
d_step_3648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_PcView_1898 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_step_3648 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.not-start
d_not'45'start_3674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   T_JumpPost_1878) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_not'45'start_3674 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.no-once
d_no'45'once_3684 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   T_JumpPost_1878) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_no'45'once_3684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15
  = du_no'45'once_3684
du_no'45'once_3684 :: AgdaAny
du_no'45'once_3684 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.jgo
d_jgo_3686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   T_JumpPost_1878) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_JumpPost_1878 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_jgo_3686 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.ret≢start
d_ret'8802'start_3718 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ret'8802'start_3718 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.go
d_go_3724 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RetMatch_1746 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_go_3724 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.prov-go
d_prov'45'go_3740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RetMatch_1746 ->
  T_RetMatch_1746 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_prov'45'go_3740 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.cl≢start
d_cl'8802'start_3754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cl'8802'start_3754 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.cgo
d_cgo_3758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cgo_3758 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.cf≢start
d_cf'8802'start_3780 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cf'8802'start_3780 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.fgo
d_fgo_3786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fgo_3786 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-stack-ptr
d_run'45'stack'45'ptr_3804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_534
d_run'45'stack'45'ptr_3804 ~v0 v1 ~v2 ~v3 v4 v5 v6
  = du_run'45'stack'45'ptr_3804 v1 v4 v5 v6
du_run'45'stack'45'ptr_3804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_534
du_run'45'stack'45'ptr_3804 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_448 v4 v5 v7 v8
        -> coe du_go_3826 (coe v0) (coe v1) (coe v2) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_3826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_534
d_go_3826 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
  = du_go_3826 v1 v4 v11 v12
du_go_3826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_534
du_go_3826 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'start_372 v5
        -> coe du_entry'45'stack'45'ptr_3374 (coe v2) (coe v5)
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'step_378 v4 v5 v6
        -> coe
             du_stack'45'ptr'45'step_2966 (coe v0) (coe v4) (coe v1) (coe v5)
             (coe du_go_3826 (coe v0) (coe v1) (coe v5) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.stack-ptr-current
d_stack'45'ptr'45'current_3850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'ptr'45'current_3850 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9
  = du_stack'45'ptr'45'current_3850
du_stack'45'ptr'45'current_3850 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'ptr'45'current_3850
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.stack-ptr-current-suc
d_stack'45'ptr'45'current'45'suc_3872 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'ptr'45'current'45'suc_3872 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 ~v9
  = du_stack'45'ptr'45'current'45'suc_3872
du_stack'45'ptr'45'current'45'suc_3872 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'ptr'45'current'45'suc_3872
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.slot-read-in-frame
d_slot'45'read'45'in'45'frame_3894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'read'45'in'45'frame_3894 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 v8
                                   ~v9 ~v10
  = du_slot'45'read'45'in'45'frame_3894 v0 v5 v6 v8
du_slot'45'read'45'in'45'frame_3894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'read'45'in'45'frame_3894 v0 v1 v2 v3
  = coe
      du_emitted'45'slot'45'below'45'budget_1720 (coe v0)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
         (coe v3))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
         (coe v3))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)) (coe v2)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.just-injI
d_just'45'injI_3918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injI_3918 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.seg-eq
d_seg'45'eq_3920 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seg'45'eq_3920 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.go
d_go_3926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_3926 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.no-slot
d_no'45'slot_3942 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_no'45'slot_3942 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16
  = du_no'45'slot_3942
du_no'45'slot_3942 :: AgdaAny
du_no'45'slot_3942 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.emitted-alloc-min
d_emitted'45'alloc'45'min_3958 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_emitted'45'alloc'45'min_3958 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8
  = du_emitted'45'alloc'45'min_3958 v0 v5 v7
du_emitted'45'alloc'45'min_3958 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_emitted'45'alloc'45'min_3958 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_4132
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_program'45'image_42
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v3)
                          (coe v5)))
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ProgramImageFacts.d_image'45'alloc'45'min_114
                       (coe v0) (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.ptr-bounds-step
d_ptr'45'bounds'45'step_3976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_574 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_574
d_ptr'45'bounds'45'step_3976 v0 v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10
                             v11
  = du_ptr'45'bounds'45'step_3976 v0 v1 v4 v5 v6 v7 v9 v10 v11
du_ptr'45'bounds'45'step_3976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_574 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_574
du_ptr'45'bounds'45'step_3976 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2268 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2276 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2284 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2286 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2288 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2290 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v12 v13 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v12 v13 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe
                (\ v10 v11 ->
                   coe
                     du_emitted'45'alloc'45'min_3958 (coe v0) (coe v4)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
                           (coe v5))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
                              (coe v5))
                           erased))))
             (coe v7) (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.d_flat'45'ptr'45'bounds_2158
             (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)) (coe v7)
             (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-wf-ptr-bounds
d_run'45'wf'45'ptr'45'bounds_4502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'wf'45'ptr'45'bounds_4502 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_run'45'wf'45'ptr'45'bounds_4502 v0 v1 v4 v5 v6
du_run'45'wf'45'ptr'45'bounds_4502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'wf'45'ptr'45'bounds_4502 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_448 v5 v6 v8 v9
        -> coe
             du_go_4524 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6) erased
             (coe v8) (coe v3) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_4524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_4524 v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12
  = du_go_4524 v0 v1 v4 v6 v7 v8 v9 v11 v12
du_go_4524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_4524 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'start_372 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_entry'45'flat'45'wf_3510 (coe v7) (coe v10))
             (coe du_entry'45'ptr'45'bounds_3442 (coe v7) (coe v10))
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'step_378 v9 v10 v11
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_flat'45'wf'45'step_2846
                (coe v1) (coe v9) (coe v2) (coe v10)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_4524 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) erased
                      (coe v6) (coe v10) (coe v11))))
             (coe
                du_ptr'45'bounds'45'step_3976 (coe v0) (coe v1) (coe v9) (coe v2)
                (coe v10)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_448
                   v3 v4 v6 v11)
                (coe
                   du_frame'45'op'45'absurd_1648 (coe v0) (coe v10)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_4524 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) erased
                      (coe v6) (coe v10) (coe v11)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      du_go_4524 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) erased
                      (coe v6) (coe v10) (coe v11))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-ptr-bounds
d_run'45'ptr'45'bounds_4548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_574
d_run'45'ptr'45'bounds_4548 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_run'45'ptr'45'bounds_4548 v0 v1 v4 v5 v6
du_run'45'ptr'45'bounds_4548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_574
du_run'45'ptr'45'bounds_4548 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_run'45'wf'45'ptr'45'bounds_4502 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-shape-check
d_run'45'shape'45'check_4564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'shape'45'check_4564 v0 v1 v2 ~v3 ~v4 ~v5 v6
  = du_run'45'shape'45'check_4564 v0 v1 v2 v6
du_run'45'shape'45'check_4564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'shape'45'check_4564 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_chk_4576 (coe v0) (coe v1) (coe v2) (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_chk_4576 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.chk
d_chk_4576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_chk_4576 v0 v1 v2 ~v3 ~v4 ~v5 v6 = du_chk_4576 v0 v1 v2 v6
du_chk_4576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_chk_4576 v0 v1 v2 v3
  = coe
      d_emitted'45'shape'45'check_1630 v0 v1 v2 erased
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
         (coe v3))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
         (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.slot-read-written
d_slot'45'read'45'written_4590 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'read'45'written_4590 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.sc
d_sc_4612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_4612 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_sc_4612 v0 v1 v2 v8
du_sc_4612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_4612 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_4564 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.env
d_env_4614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_env_4614 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_env_4614 v0 v1 v2 v8
du_env_4614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_env_4614 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_4612 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.chk
d_chk_4616 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_4616 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.st
d_st_4618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_st_4618 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_st_4618 v0 v1 v2 v4 v5 v8
du_st_4618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_st_4618 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_1026
      (coe du_env_4614 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_1008
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v4))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.claim
d_claim_4620 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_claim_4620 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.met
d_met_4622 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_met_4622 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_met_4622 v0 v1 v2 v4 v5 v6 v8
du_met_4622 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  AgdaAny
du_met_4622 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            d_run'45'meets_1638 v0 v1 v2 erased v3 v4 v6
            (coe du_env_4614 (coe v0) (coe v1) (coe v2) (coe v6)) erased))
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.load-indirect-target-ptr
d_load'45'indirect'45'target'45'ptr_4632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'target'45'ptr_4632 v0 v1 v2 ~v3 v4 v5 v6 ~v7
  = du_load'45'indirect'45'target'45'ptr_4632 v0 v1 v2 v4 v5 v6
du_load'45'indirect'45'target'45'ptr_4632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'target'45'ptr_4632 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2446
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe
            du_st_4652 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v4)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1638 v0 v1 v2 erased v3 v4 v5
            (coe du_env_4648 (coe v0) (coe v1) (coe v2) (coe v5)) erased))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.sc
d_sc_4646 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_4646 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_sc_4646 v0 v1 v2 v6
du_sc_4646 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_4646 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_4564 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.env
d_env_4648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_env_4648 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_env_4648 v0 v1 v2 v6
du_env_4648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_env_4648 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_4646 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.chk
d_chk_4650 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_4650 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.st
d_st_4652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_st_4652 v0 v1 v2 ~v3 v4 v5 v6 ~v7 = du_st_4652 v0 v1 v2 v4 v5 v6
du_st_4652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_st_4652 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_1026
      (coe du_env_4648 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_1008
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v4))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ok
d_ok_4654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_4654 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.out-nz-output-word
d_out'45'nz'45'output'45'word_4662 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_out'45'nz'45'output'45'word_4662 v0 v1 v2 ~v3 v4 v5 v6 ~v7
  = du_out'45'nz'45'output'45'word_4662 v0 v1 v2 v4 v5 v6
du_out'45'nz'45'output'45'word_4662 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_out'45'nz'45'output'45'word_4662 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'out'45'word_3320
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'out_36
         (coe
            du_st_4682 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_run'45'meets_1638 v0 v1 v2 erased v3 v4 v5
               (coe du_env_4678 (coe v0) (coe v1) (coe v2) (coe v5)) erased)))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.sc
d_sc_4676 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_4676 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_sc_4676 v0 v1 v2 v6
du_sc_4676 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_4676 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_4564 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.env
d_env_4678 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_env_4678 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_env_4678 v0 v1 v2 v6
du_env_4678 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_env_4678 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_4676 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.chk
d_chk_4680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_4680 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.st
d_st_4682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_st_4682 v0 v1 v2 ~v3 v4 v5 v6 ~v7 = du_st_4682 v0 v1 v2 v4 v5 v6
du_st_4682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_st_4682 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_1026
      (coe du_env_4678 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_1008
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v4))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ok
d_ok_4684 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_4684 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.load-indirect-suc-target-ptr
d_load'45'indirect'45'suc'45'target'45'ptr_4692 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'target'45'ptr_4692 v0 v1 v2 ~v3 v4 v5
                                                v6 ~v7
  = du_load'45'indirect'45'suc'45'target'45'ptr_4692
      v0 v1 v2 v4 v5 v6
du_load'45'indirect'45'suc'45'target'45'ptr_4692 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'target'45'ptr_4692 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2446
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe
            du_st_4712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v4)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1638 v0 v1 v2 erased v3 v4 v5
            (coe du_env_4708 (coe v0) (coe v1) (coe v2) (coe v5)) erased))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.sc
d_sc_4706 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_4706 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_sc_4706 v0 v1 v2 v6
du_sc_4706 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_4706 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_4564 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.env
d_env_4708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_env_4708 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_env_4708 v0 v1 v2 v6
du_env_4708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_env_4708 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_4706 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.chk
d_chk_4710 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_4710 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.st
d_st_4712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_st_4712 v0 v1 v2 ~v3 v4 v5 v6 ~v7 = du_st_4712 v0 v1 v2 v4 v5 v6
du_st_4712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_st_4712 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_1026
      (coe du_env_4708 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_1008
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v4))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ok
d_ok_4714 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_4714 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.store-indirect-target-ptr
d_store'45'indirect'45'target'45'ptr_4722 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'target'45'ptr_4722 v0 v1 v2 ~v3 v4 v5 v6 ~v7
  = du_store'45'indirect'45'target'45'ptr_4722 v0 v1 v2 v4 v5 v6
du_store'45'indirect'45'target'45'ptr_4722 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'target'45'ptr_4722 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'store'45'ptr_3302
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe
            du_st_4742 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v4)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1638 v0 v1 v2 erased v3 v4 v5
            (coe du_env_4738 (coe v0) (coe v1) (coe v2) (coe v5)) erased))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.sc
d_sc_4736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_4736 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_sc_4736 v0 v1 v2 v6
du_sc_4736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_4736 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_4564 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.env
d_env_4738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_env_4738 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_env_4738 v0 v1 v2 v6
du_env_4738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_env_4738 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_4736 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.chk
d_chk_4740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_4740 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.st
d_st_4742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_st_4742 v0 v1 v2 ~v3 v4 v5 v6 ~v7 = du_st_4742 v0 v1 v2 v4 v5 v6
du_st_4742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_st_4742 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_1026
      (coe du_env_4738 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_1008
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v4))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ok
d_ok_4744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_4744 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.store-indirect-suc-target-ptr
d_store'45'indirect'45'suc'45'target'45'ptr_4752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'suc'45'target'45'ptr_4752 v0 v1 v2 ~v3 v4 v5
                                                 v6 ~v7
  = du_store'45'indirect'45'suc'45'target'45'ptr_4752
      v0 v1 v2 v4 v5 v6
du_store'45'indirect'45'suc'45'target'45'ptr_4752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'suc'45'target'45'ptr_4752 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'store'45'ptr_3302
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
         (coe
            du_st_4772 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v4)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_run'45'meets_1638 v0 v1 v2 erased v3 v4 v5
            (coe du_env_4768 (coe v0) (coe v1) (coe v2) (coe v5)) erased))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.sc
d_sc_4766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_4766 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_sc_4766 v0 v1 v2 v6
du_sc_4766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_4766 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_4564 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.env
d_env_4768 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_env_4768 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_env_4768 v0 v1 v2 v6
du_env_4768 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_env_4768 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_4766 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.chk
d_chk_4770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_4770 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.st
d_st_4772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_st_4772 v0 v1 v2 ~v3 v4 v5 v6 ~v7 = du_st_4772 v0 v1 v2 v4 v5 v6
du_st_4772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_st_4772 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_1026
      (coe du_env_4768 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_1008
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v4))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ok
d_ok_4774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_4774 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.store-nonptr-absurd
d_store'45'nonptr'45'absurd_4784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_store'45'nonptr'45'absurd_4784 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.wits
d_wits_4802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_4802 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_wits_4802 v0 v1 v2 v4 v5 v7
du_wits_4802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_4802 v0 v1 v2 v3 v4 v5
  = coe
      du_store'45'indirect'45'target'45'ptr_4722 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.store-suc-nonptr-absurd
d_store'45'suc'45'nonptr'45'absurd_4812 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_store'45'suc'45'nonptr'45'absurd_4812 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.wits
d_wits_4830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_4830 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_wits_4830 v0 v1 v2 v4 v5 v7
du_wits_4830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_4830 v0 v1 v2 v3 v4 v5
  = coe
      du_store'45'indirect'45'suc'45'target'45'ptr_4752 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.branch-tag-scrutinee-wf
d_branch'45'tag'45'scrutinee'45'wf_4842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_branch'45'tag'45'scrutinee'45'wf_4842 v0 v1 v2 ~v3 v4 v5 ~v6 v7
                                        ~v8
  = du_branch'45'tag'45'scrutinee'45'wf_4842 v0 v1 v2 v4 v5 v7
du_branch'45'tag'45'scrutinee'45'wf_4842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'45'tag'45'scrutinee'45'wf_4842 v0 v1 v2 v3 v4 v5
  = coe
      du_repack_4876
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'branch'45'tag_2618
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
            (coe
               du_st_4864 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v4)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_run'45'meets_1638 v0 v1 v2 erased v3 v4 v5
               (coe du_env_4860 (coe v0) (coe v1) (coe v2) (coe v5)) erased)))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.sc
d_sc_4858 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sc_4858 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 = du_sc_4858 v0 v1 v2 v7
du_sc_4858 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sc_4858 v0 v1 v2 v3
  = coe
      du_run'45'shape'45'check_4564 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.env
d_env_4860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_env_4860 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_env_4860 v0 v1 v2 v7
du_env_4860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_env_4860 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_sc_4858 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.chk
d_chk_4862 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chk_4862 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.st
d_st_4864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
d_st_4864 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8
  = du_st_4864 v0 v1 v2 v4 v5 v7
du_st_4864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_26
du_st_4864 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_1026
      (coe du_env_4860 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_1008
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
      (coe v3) (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v4))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.ok
d_ok_4866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok_4866 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.repack
d_repack_4876 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_repack_4876 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_repack_4876 v9
du_repack_4876 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_repack_4876 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.store-indirect-inbounds
d_store'45'indirect'45'inbounds_4892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_store'45'indirect'45'inbounds_4892 v0 v1 ~v2 ~v3 v4 v5 v6 v7 ~v8
                                     ~v9
  = du_store'45'indirect'45'inbounds_4892 v0 v1 v4 v5 v6 v7
du_store'45'indirect'45'inbounds_4892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_store'45'indirect'45'inbounds_4892 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'cell_638
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v4)
      (coe
         du_run'45'ptr'45'bounds_4548 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.store-indirect-suc-inbounds
d_store'45'indirect'45'suc'45'inbounds_4912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_store'45'indirect'45'suc'45'inbounds_4912 v0 v1 ~v2 ~v3 v4 v5 ~v6
                                            v7 ~v8 ~v9
  = du_store'45'indirect'45'suc'45'inbounds_4912 v0 v1 v4 v5 v7
du_store'45'indirect'45'suc'45'inbounds_4912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_store'45'indirect'45'suc'45'inbounds_4912 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'suc_620
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
      (coe
         du_run'45'ptr'45'bounds_4548 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.load-indirect-target-wf
d_load'45'indirect'45'target'45'wf_4934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'target'45'wf_4934 v0 v1 v2 ~v3 v4 v5 v6 ~v7
  = du_load'45'indirect'45'target'45'wf_4934 v0 v1 v2 v4 v5 v6
du_load'45'indirect'45'target'45'wf_4934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'target'45'wf_4934 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2446
              (coe
                 MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
                 (coe
                    MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_1026
                    (coe du_env_4648 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_1008
                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                    (coe v3)
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v4))))
              (coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                 (coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v4)))
                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    d_run'45'meets_1638 v0 v1 v2 erased v3 v4 v5
                    (coe du_env_4648 (coe v0) (coe v1) (coe v2) (coe v5)) erased)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                   (coe
                      (\ v9 v10 ->
                         coe
                           MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'cell_638
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v9)
                           (coe
                              du_run'45'ptr'45'bounds_4548 (coe v0) (coe v1) (coe v3) (coe v4)
                              (coe v5)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.load-indirect-suc-target-wf
d_load'45'indirect'45'suc'45'target'45'wf_4972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'target'45'wf_4972 v0 v1 v2 ~v3 v4 v5
                                               v6 ~v7
  = du_load'45'indirect'45'suc'45'target'45'wf_4972 v0 v1 v2 v4 v5 v6
du_load'45'indirect'45'suc'45'target'45'wf_4972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'target'45'wf_4972 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.Codegen.ShapeTable.du_site'45'load'45'ptr_2446
              (coe
                 MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_e'45'in1_34
                 (coe
                    MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_state'45'at_1026
                    (coe du_env_4708 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_entry'45'expect_1008
                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                    (coe v3)
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v4))))
              (coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                 (coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v4)))
                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    d_run'45'meets_1638 v0 v1 v2 erased v3 v4 v5
                    (coe du_env_4708 (coe v0) (coe v1) (coe v2) (coe v5)) erased)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                   (coe
                      (\ v9 v10 ->
                         coe
                           MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.du_ptr'45'bounds'45'suc_620
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
                           (coe
                              du_run'45'ptr'45'bounds_4548 (coe v0) (coe v1) (coe v3) (coe v4)
                              (coe v5)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.nothing≢justℕ
d_nothing'8802'justℕ_5004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'justℕ_5004 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-link-at-thunk
d_run'45'link'45'at'45'thunk_5016 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'link'45'at'45'thunk_5016 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 ~v7
  = du_run'45'link'45'at'45'thunk_5016 v1 v4 v6
du_run'45'link'45'at'45'thunk_5016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'link'45'at'45'thunk_5016 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_448 v3 v4 v6 v7
        -> coe (\ v8 -> coe du_go_5048 (coe v0) (coe v1) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.Goal
d_Goal_5036 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_Goal_5036 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.go
d_go_5048 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_5048 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 v13
          ~v14 ~v15
  = du_go_5048 v1 v4 v13
du_go_5048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_5048 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'start_372 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                    -> case coe v13 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                           -> case coe v15 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                  -> case coe v17 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                         -> case coe v19 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                -> coe
                                                                     seq (coe v21)
                                                                     (coe
                                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'step_378 v3 v4 v5
        -> coe
             du_step_5088 (coe v0) (coe v1) (coe v4)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flinkView_3476 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.ih-thunk
d_ih'45'thunk_5078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ih'45'thunk_5078 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_ih'45'thunk_5078 v1 v4 v14
du_ih'45'thunk_5078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ih'45'thunk_5078 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_ihr_5086 (coe v0) (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe du_ihr_5086 (coe v0) (coe v1) (coe v2))))
         erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.ihr
d_ihr_5086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ihr_5086 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_ihr_5086 v1 v4 v14
du_ihr_5086 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ihr_5086 v0 v1 v2 = coe du_go_5048 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._.step
d_step_5088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3448 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_5088 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19
  = du_step_5088 v1 v4 v13 v19
du_step_5088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlinkView_3448 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_5088 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.Flat.C_fv'45'call_3452
        -> coe
             du_call'45'step_5100 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1368 (coe v0)
                (coe v1) (coe v2))
      MAlonzo.Code.Once.CCC.Machine.Flat.C_fv'45'call'45'fn_3456 v4
        -> coe
             du_cf'45'step_5168 (coe v0) (coe v1) (coe v4)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240 (coe v0)
                (coe v1) (coe v4))
      MAlonzo.Code.Once.CCC.Machine.Flat.C_fv'45'thunk_3462 v4 v5
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.Flat.C_fv'45'start_3466 v4
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.Flat.C_fv'45'pres_3472
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.red
d_red_5096 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_5096 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.call-step
d_call'45'step_5100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_call'45'step_5100 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                    ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_call'45'step_5100 v1 v4 v20
du_call'45'step_5100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_call'45'step_5100 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Flat.C_cp'45'halt_1356
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.Flat.C_cp'45'enter_1362 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_fts_5136 (coe v0) (coe v1) (coe v3) (coe v4)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe du_fts_5136 (coe v0) (coe v1) (coe v3) (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.pre
d_pre_5108 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pre_5108 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.thunk≢call
d_thunk'8802'call_5114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_thunk'8802'call_5114 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.fts
d_fts_5136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fts_5136 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 v21 ~v22 ~v23
  = du_fts_5136 v1 v4 v20 v21
du_fts_5136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fts_5136 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk'45'sound_916 v0
      v1 v2 v3 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.red
d_red_5148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_5148 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.entry≢callfn
d_entry'8802'callfn_5156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_entry'8802'callfn_5156 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.cf-step
d_cf'45'step_5168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cf'45'step_5168 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22
  = du_cf'45'step_5168 v1 v4 v19 v21
du_cf'45'step_5168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cf'45'step_5168 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_fes_5188 (coe v0) (coe v1) (coe v2) (coe v4)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe du_fes_5188 (coe v0) (coe v1) (coe v2) (coe v4))))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.pre
d_pre_5176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pre_5176 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._._.fes
d_fes_5188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fes_5188 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22
  = du_fes_5188 v1 v4 v19 v21
du_fes_5188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fes_5188 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_find'45'entry'45'sound_882
      (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v2)) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.cleared
d_cleared_5204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cleared_5204 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.cleared
d_cleared_5216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cleared_5216 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.pre
d_pre_5226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pre_5226 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.ihr
d_ihr_5228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ihr_5228 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_ihr_5228 v1 v4 v14
du_ihr_5228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ihr_5228 v0 v1 v2
  = coe du_ih'45'thunk_5078 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._._._.cleared
d_cleared_5230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cleared_5230 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-link-nothing-aux
d_run'45'link'45'nothing'45'aux_5244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'link'45'nothing'45'aux_5244 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF._.res
d_res_5272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_res_5272 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_res_5272 v1 v4 v6
du_res_5272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_res_5272 v0 v1 v2
  = coe du_run'45'link'45'at'45'thunk_5016 v0 v1 v2 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF.run-link-nothing
d_run'45'link'45'nothing_5282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'link'45'nothing_5282 = erased
