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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatSimulation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.FloatBits
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.FlatState
d_FlatState_16 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch
d_fetch_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch_64 ~v0 ~v1 = du_fetch_64
du_fetch_64 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_fetch_64 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.find-label
d_find'45'label_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Maybe Integer
d_find'45'label_72 v0 ~v1 = du_find'45'label_72 v0
du_find'45'label_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Maybe Integer
du_find'45'label_72 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_158 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.flat-exec-instr
d_flat'45'exec'45'instr_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_84 v0 ~v1 = du_flat'45'exec'45'instr_84 v0
du_flat'45'exec'45'instr_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_flat'45'exec'45'instr_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.flat-read-tag
d_flat'45'read'45'tag_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_flat'45'read'45'tag_88 ~v0 ~v1 = du_flat'45'read'45'tag_88
du_flat'45'read'45'tag_88 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_flat'45'read'45'tag_88
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_108
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.leave-frame
d_leave'45'frame_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame_112 ~v0 ~v1 = du_leave'45'frame_112
du_leave'45'frame_112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame_112
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_266
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.sv-is-zero
d_sv'45'is'45'zero_138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_sv'45'is'45'zero_138 ~v0 ~v1 = du_sv'45'is'45'zero_138
du_sv'45'is'45'zero_138 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_sv'45'is'45'zero_138
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_94
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.tag-zf
d_tag'45'zf_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_tag'45'zf_140 ~v0 ~v1 = du_tag'45'zf_140
du_tag'45'zf_140 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_tag'45'zf_140
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_96
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.FlatState.falloc
d_falloc_148 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_148 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.FlatState.fclosure
d_fclosure_150 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_150 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.FlatState.floc
d_floc_152 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_152 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.FlatState.fpc
d_fpc_154 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_154 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.FlatState.fret
d_fret_156 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_156 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.sv-below
d_sv'45'below_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_168 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.svm-below
d_svm'45'below_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_svm'45'below_170 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.+-not-<
d_'43''45'not'45''60'_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_192 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.AddrMap
d_AddrMap_194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> ()
d_AddrMap_194 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.ExtDom
d_ExtDom_196 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr
d_FlatCorr_198 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.HDom
d_HDom_202 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_202 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.HeapView
d_HeapView_204 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.StackWindows
d_StackWindows_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_StackWindows_208 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.Window
d_Window_210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny -> Integer -> ()
d_Window_210 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.atstack-frame-inj
d_atstack'45'frame'45'inj_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'frame'45'inj_212 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.atstack-slot-inj
d_atstack'45'slot'45'inj_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_214 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.dec-enc
d_dec'45'enc_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_216 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.descend-view
d_descend'45'view_218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
d_descend'45'view_218 ~v0 ~v1 = du_descend'45'view_218
du_descend'45'view_218 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
du_descend'45'view_218 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_descend'45'view_586
      v0 v1 v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.dom-below
d_dom'45'below_220 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_220 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'below_262
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.dom-fresh
d_dom'45'fresh_222 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_222 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'fresh_436
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.dom-sized
d_dom'45'sized_224 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_224 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'sized_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.dom-written
d_dom'45'written_226 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_226 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'written_442
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.enc-ext
d_enc'45'ext_228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext_228 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.enc-ext-maybe
d_enc'45'ext'45'maybe_230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext'45'maybe_230 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.enc-maybe
d_enc'45'maybe_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe_232 v0 ~v1 = du_enc'45'maybe_232 v0
du_enc'45'maybe_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe_232 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'maybe_316
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.enc-maybe-at
d_enc'45'maybe'45'at_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe'45'at_234 v0 ~v1 = du_enc'45'maybe'45'at_234 v0
du_enc'45'maybe'45'at_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe'45'at_234 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'maybe'45'at_304
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.enc-sv
d_enc'45'sv_236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv_236 v0 ~v1 = du_enc'45'sv_236 v0
du_enc'45'sv_236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv_236 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.enc-sv-at
d_enc'45'sv'45'at_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv'45'at_238 v0 ~v1 = du_enc'45'sv'45'at_238 v0
du_enc'45'sv'45'at_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv'45'at_238 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv'45'at_276
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.enc-zero
d_enc'45'zero_240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_240 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.ext-addr
d_ext'45'addr_242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_242 ~v0 ~v1 = du_ext'45'addr_242
du_ext'45'addr_242 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_242
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_ext'45'addr_2184
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.ext-addr-aux
d_ext'45'addr'45'aux_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_244 ~v0 ~v1 = du_ext'45'addr'45'aux_244
du_ext'45'addr'45'aux_244 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_244 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_ext'45'addr'45'aux_2166
      v0 v1 v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.ext-addr-base
d_ext'45'addr'45'base_246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_246 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.ext-addr-fresh
d_ext'45'addr'45'fresh_248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_248 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.ext-addr-old
d_ext'45'addr'45'old_250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_250 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.ext-suc
d_ext'45'suc_256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_256 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.ext-suc-aux
d_ext'45'suc'45'aux_258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_258 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.extend-view
d_extend'45'view_260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
d_extend'45'view_260 ~v0 ~v1 = du_extend'45'view_260
du_extend'45'view_260 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218
du_extend'45'view_260 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_extend'45'view_2342
      v0 v1 v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.frames-of
d_frames'45'of_262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_frames'45'of_262 ~v0 ~v1 = du_frames'45'of_262
du_frames'45'of_262 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_frames'45'of_262
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_frames'45'of_320
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.front-lo
d_front'45'lo_264 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_264 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_266
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.haddr
d_haddr_266 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_266 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_haddr_244
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.haddr-inj
d_haddr'45'inj_268 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_268 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.haddr-suc
d_haddr'45'suc_270 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_270 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.halt-eq
d_halt'45'eq_272 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_272 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.heap-eq
d_heap'45'eq_274 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_274 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.hfront
d_hfront_276 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_hfront_276 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_hfront_248
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.inc-enc
d_inc'45'enc_278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_278 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.lit-word
d_lit'45'word_280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer
d_lit'45'word_280 ~v0 ~v1 v2 = du_lit'45'word_280 v2
du_lit'45'word_280 :: Integer -> Integer
du_lit'45'word_280 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.lo
d_lo_282 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_lo_282 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo_264
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.lo-le
d_lo'45'le_284 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_284 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo'45'le_452
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.r14-eq
d_r14'45'eq_288 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r14'45'eq_288 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.r15-eq
d_r15'45'eq_290 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r15'45'eq_290 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.rax-eq
d_rax'45'eq_292 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rax'45'eq_292 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.rbx-eq
d_rbx'45'eq_294 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'eq_294 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.rdi-eq
d_rdi'45'eq_296 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'eq_296 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.read-write-miss
d_read'45'write'45'miss_298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'miss_298 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.rsi-eq
d_rsi'45'eq_300 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsi'45'eq_300 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.rsp-eq
d_rsp'45'eq_302 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsp'45'eq_302 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sep
d_sep_304 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sep_304 v0 ~v1 ~v2 v3 = du_sep_304 v0 v3
du_sep_304 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sep_304 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_266
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo'45'le_452
         (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-alloc-heap
d_sim'45'alloc'45'heap_306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'alloc'45'heap_306 ~v0 ~v1 = du_sim'45'alloc'45'heap_306
du_sim'45'alloc'45'heap_306 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'alloc'45'heap_306 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'alloc'45'heap_2680
      v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-alloc-stack
d_sim'45'alloc'45'stack_308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'alloc'45'stack_308 v0 ~v1
  = du_sim'45'alloc'45'stack_308 v0
du_sim'45'alloc'45'stack_308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'alloc'45'stack_308 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'alloc'45'stack_1916
      (coe v0) v2 v4 v6 v12
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-dealloc-stack
d_sim'45'dealloc'45'stack_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'dealloc'45'stack_310 v0 ~v1
  = du_sim'45'dealloc'45'stack_310 v0
du_sim'45'dealloc'45'stack_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'dealloc'45'stack_310 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'dealloc'45'stack_1980
      (coe v0) v4 v5 v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-lea-slot
d_sim'45'lea'45'slot_312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'lea'45'slot_312 ~v0 ~v1 = du_sim'45'lea'45'slot_312
du_sim'45'lea'45'slot_312 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'lea'45'slot_312 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'lea'45'slot_2796
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-load-code-addr
d_sim'45'load'45'code'45'addr_314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'code'45'addr_314 ~v0 ~v1
  = du_sim'45'load'45'code'45'addr_314
du_sim'45'load'45'code'45'addr_314 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'code'45'addr_314 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'code'45'addr_2056
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-load-const
d_sim'45'load'45'const_316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'const_316 ~v0 ~v1 = du_sim'45'load'45'const_316
du_sim'45'load'45'const_316 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'const_316 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'const_2016
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-load-const-float
d_sim'45'load'45'const'45'float_318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'const'45'float_318 ~v0 ~v1
  = du_sim'45'load'45'const'45'float_318
du_sim'45'load'45'const'45'float_318 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'const'45'float_318 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'const'45'float_2036
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-load-from-slot
d_sim'45'load'45'from'45'slot_320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'from'45'slot_320 ~v0 ~v1
  = du_sim'45'load'45'from'45'slot_320
du_sim'45'load'45'from'45'slot_320 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'from'45'slot_320 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'from'45'slot_898
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-load-indirect
d_sim'45'load'45'indirect_322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'indirect_322 ~v0 ~v1
  = du_sim'45'load'45'indirect_322
du_sim'45'load'45'indirect_322 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'indirect_322 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect_848
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-load-indirect-stack
d_sim'45'load'45'indirect'45'stack_324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'indirect'45'stack_324 ~v0 ~v1
  = du_sim'45'load'45'indirect'45'stack_324
du_sim'45'load'45'indirect'45'stack_324 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'indirect'45'stack_324 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'stack_2832
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'indirect'45'suc_326 ~v0 ~v1
  = du_sim'45'load'45'indirect'45'suc_326
du_sim'45'load'45'indirect'45'suc_326 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'indirect'45'suc_326 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc_798
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-load-indirect-suc-stack
d_sim'45'load'45'indirect'45'suc'45'stack_328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'indirect'45'suc'45'stack_328 ~v0 ~v1
  = du_sim'45'load'45'indirect'45'suc'45'stack_328
du_sim'45'load'45'indirect'45'suc'45'stack_328 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'indirect'45'suc'45'stack_328 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc'45'stack_2886
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'load'45'tag'45'lit_330 ~v0 ~v1
  = du_sim'45'load'45'tag'45'lit_330
du_sim'45'load'45'tag'45'lit_330 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'load'45'tag'45'lit_330 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'tag'45'lit_698
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-mov-input2-to-output
d_sim'45'mov'45'input2'45'to'45'output_332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'input2'45'to'45'output_332 ~v0 ~v1
  = du_sim'45'mov'45'input2'45'to'45'output_332
du_sim'45'mov'45'input2'45'to'45'output_332 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'input2'45'to'45'output_332 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'input2'45'to'45'output_664
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-mov-output-to-input2
d_sim'45'mov'45'output'45'to'45'input2_334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'output'45'to'45'input2_334 ~v0 ~v1
  = du_sim'45'mov'45'output'45'to'45'input2_334
du_sim'45'mov'45'output'45'to'45'input2_334 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'output'45'to'45'input2_334 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'output'45'to'45'input2_680
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-mov-to-input
d_sim'45'mov'45'to'45'input_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'to'45'input_336 ~v0 ~v1
  = du_sim'45'mov'45'to'45'input_336
du_sim'45'mov'45'to'45'input_336 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'to'45'input_336 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'to'45'input_648
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-mov-to-output
d_sim'45'mov'45'to'45'output_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'mov'45'to'45'output_338 ~v0 ~v1
  = du_sim'45'mov'45'to'45'output_338
du_sim'45'mov'45'to'45'output_338 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'mov'45'to'45'output_338 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'to'45'output_632
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-reg-count-inc
d_sim'45'reg'45'count'45'inc_340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'count'45'inc_340 ~v0 ~v1
  = du_sim'45'reg'45'count'45'inc_340
du_sim'45'reg'45'count'45'inc_340 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'count'45'inc_340 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'count'45'inc_2114
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-reg-count-zero
d_sim'45'reg'45'count'45'zero_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'count'45'zero_342 ~v0 ~v1
  = du_sim'45'reg'45'count'45'zero_342
du_sim'45'reg'45'count'45'zero_342 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'count'45'zero_342 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'count'45'zero_748
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'dec_344 ~v0 ~v1
  = du_sim'45'reg'45'scratch'45'dec_344
du_sim'45'reg'45'scratch'45'dec_344 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'dec_344 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'dec_2142
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'load'45'count_346 ~v0 ~v1
  = du_sim'45'reg'45'scratch'45'load'45'count_346
du_sim'45'reg'45'scratch'45'load'45'count_346 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'load'45'count_346 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'load'45'count_764
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'one_348 ~v0 ~v1
  = du_sim'45'reg'45'scratch'45'one_348
du_sim'45'reg'45'scratch'45'one_348 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'one_348 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'one_716
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'reg'45'scratch'45'zero_350 ~v0 ~v1
  = du_sim'45'reg'45'scratch'45'zero_350
du_sim'45'reg'45'scratch'45'zero_350 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'reg'45'scratch'45'zero_350 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'zero_732
      v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-restore-input
d_sim'45'restore'45'input_352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'restore'45'input_352 ~v0 ~v1
  = du_sim'45'restore'45'input_352
du_sim'45'restore'45'input_352 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'restore'45'input_352 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'restore'45'input_1592
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_354 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'save'45'closure'45'reg_354 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-store-at-slot
d_sim'45'store'45'at'45'slot_356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'store'45'at'45'slot_356 ~v0 ~v1
  = du_sim'45'store'45'at'45'slot_356
du_sim'45'store'45'at'45'slot_356 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'at'45'slot_356 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'at'45'slot_1864
      v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-store-indirect
d_sim'45'store'45'indirect_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'store'45'indirect_358 ~v0 ~v1
  = du_sim'45'store'45'indirect_358
du_sim'45'store'45'indirect_358 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'indirect_358 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect_1494
      v1 v2 v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-store-indirect-stack
d_sim'45'store'45'indirect'45'stack_360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'store'45'indirect'45'stack_360 ~v0 ~v1
  = du_sim'45'store'45'indirect'45'stack_360
du_sim'45'store'45'indirect'45'stack_360 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'indirect'45'stack_360 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'stack_2938
      v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'store'45'indirect'45'suc_362 ~v0 ~v1
  = du_sim'45'store'45'indirect'45'suc_362
du_sim'45'store'45'indirect'45'suc_362 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'indirect'45'suc_362 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc_1542
      v1 v2 v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sim-store-indirect-suc-stack
d_sim'45'store'45'indirect'45'suc'45'stack_364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_sim'45'store'45'indirect'45'suc'45'stack_364 ~v0 ~v1
  = du_sim'45'store'45'indirect'45'suc'45'stack_364
du_sim'45'store'45'indirect'45'suc'45'stack_364 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_sim'45'store'45'indirect'45'suc'45'stack_364 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc'45'stack_2994
      v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.slot-addr-inj
d_slot'45'addr'45'inj_366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_366 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.stack-eq
d_stack'45'eq_368 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_368 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_stack'45'eq_458
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.stack-eq-cur
d_stack'45'eq'45'cur_370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'cur_370 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.stack-eq-win
d_stack'45'eq'45'win_372 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'win_372 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.store-dom-written
d_store'45'dom'45'written_374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
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
d_store'45'dom'45'written_374 ~v0 ~v1
  = du_store'45'dom'45'written_374
du_store'45'dom'45'written_374 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
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
du_store'45'dom'45'written_374 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_store'45'dom'45'written_1160
      v1 v4 v5 v6 v7 v8
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.store-heap-eq
d_store'45'heap'45'eq_376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'heap'45'eq_376 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'heap'45'eq_378 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'stack'45'eq_380 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.sv-tag-zero
d_sv'45'tag'45'zero_382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_382 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.untouched
d_untouched_384 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_384 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.untouched-descend
d_untouched'45'descend_386 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'descend_386 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.untouched-heap-store
d_untouched'45'heap'45'store_388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'heap'45'store_388 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.untouched-stack-store
d_untouched'45'stack'45'store_390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'stack'45'store_390 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.untouched-write
d_untouched'45'write_392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'write_392 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.win-at
d_win'45'at_394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'at_394 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.win-off
d_win'45'off_396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'off_396 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.windows-above
d_windows'45'above_398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
d_windows'45'above_398 ~v0 ~v1 = du_windows'45'above_398
du_windows'45'above_398 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
du_windows'45'above_398 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'above_1350
      v6 v9
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.windows-enc-ext
d_windows'45'enc'45'ext_400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
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
d_windows'45'enc'45'ext_400 ~v0 ~v1 = du_windows'45'enc'45'ext_400
du_windows'45'enc'45'ext_400 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
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
du_windows'45'enc'45'ext_400 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'enc'45'ext_2600
      v8 v10
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.windows-heap-store
d_windows'45'heap'45'store_402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'heap'45'store_402 ~v0 ~v1
  = du_windows'45'heap'45'store_402
du_windows'45'heap'45'store_402 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'heap'45'store_402 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'heap'45'store_1470
      v1 v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.windows-leave
d_windows'45'leave_404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'leave_404 v0 ~v1 = du_windows'45'leave_404 v0
du_windows'45'leave_404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'leave_404 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'leave_1284
      (coe v0) v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.windows-reanchor
d_windows'45'reanchor_406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
d_windows'45'reanchor_406 ~v0 ~v1 = du_windows'45'reanchor_406
du_windows'45'reanchor_406 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
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
du_windows'45'reanchor_406 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'reanchor_1256
      v8 v9
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.windows-slot-store
d_windows'45'slot'45'store_408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'slot'45'store_408 ~v0 ~v1
  = du_windows'45'slot'45'store_408
du_windows'45'slot'45'store_408 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'slot'45'store_408 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'slot'45'store_1796
      v8 v10
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.windows-write-below
d_windows'45'write'45'below_410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'write'45'below_410 ~v0 ~v1
  = du_windows'45'write'45'below_410
du_windows'45'write'45'below_410 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_windows'45'write'45'below_410 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_windows'45'write'45'below_1428
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.≡ᵇ-refl
d_'8801''7495''45'refl_412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_412 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_414 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.dom-fresh
d_dom'45'fresh_424 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_424 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'fresh_436
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.dom-sized
d_dom'45'sized_426 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_426 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'sized_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.dom-written
d_dom'45'written_428 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_428 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'written_442
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.halt-eq
d_halt'45'eq_430 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_430 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.heap-eq
d_heap'45'eq_432 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_432 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.lo-le
d_lo'45'le_434 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_434 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo'45'le_452
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.r14-eq
d_r14'45'eq_436 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r14'45'eq_436 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.r15-eq
d_r15'45'eq_438 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r15'45'eq_438 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.rax-eq
d_rax'45'eq_440 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rax'45'eq_440 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.rbx-eq
d_rbx'45'eq_442 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'eq_442 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.rdi-eq
d_rdi'45'eq_444 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'eq_444 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.rsi-eq
d_rsi'45'eq_446 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsi'45'eq_446 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.rsp-eq
d_rsp'45'eq_448 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rsp'45'eq_448 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.stack-eq
d_stack'45'eq_450 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_450 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_stack'45'eq_458
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.FlatCorr.untouched
d_untouched_452 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_452 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.HeapView.HDom
d_HDom_456 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_456 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.HeapView.dom-below
d_dom'45'below_458 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_458 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_dom'45'below_262
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.HeapView.front-lo
d_front'45'lo_460 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_460 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_front'45'lo_266
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.HeapView.haddr
d_haddr_462 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_462 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_haddr_244
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.HeapView.haddr-inj
d_haddr'45'inj_464 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_464 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.HeapView.haddr-suc
d_haddr'45'suc_466 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_466 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.HeapView.hfront
d_hfront_468 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_hfront_468 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_hfront_248
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.C.HeapView.lo
d_lo_470 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  Integer
d_lo_470 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.d_lo_264
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.x86-len
d_x86'45'len_488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer
d_x86'45'len_488 ~v0 ~v1 = du_x86'45'len_488
du_x86'45'len_488 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer
du_x86'45'len_488
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition.du_x86'45'len_156
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.x86-off
d_x86'45'off_490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer
d_x86'45'off_490 ~v0 ~v1 = du_x86'45'off_490
du_x86'45'off_490 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer
du_x86'45'off_490
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition.du_x86'45'off_160
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.readLoc
d_readLoc_496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_496 ~v0 ~v1 = du_readLoc_496
du_readLoc_496 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_496
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.writeLoc
d_writeLoc_498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLoc_498 v0 ~v1 = du_writeLoc_498 v0
du_writeLoc_498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLoc_498 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_792 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.writeLocToHeap
d_writeLocToHeap_500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToHeap_500 ~v0 ~v1 = du_writeLocToHeap_500
du_writeLocToHeap_500 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLocToHeap_500
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_784
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.CompiledCorr
d_CompiledCorr_510 a0 a1 a2 a3 a4 a5 = ()
newtype T_CompiledCorr_510
  = C_constructor_528 MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.CompiledCorr.dataCorr
d_dataCorr_524 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataCorr_524 v0
  = case coe v0 of
      C_constructor_528 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.CompiledCorr.pc-off
d_pc'45'off_526 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_526 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.b-mov-reg-reg
d_b'45'mov'45'reg'45'reg_538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b'45'mov'45'reg'45'reg_538 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.b-mov-reg-imm
d_b'45'mov'45'reg'45'imm_556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b'45'mov'45'reg'45'imm_556 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.b-cmp-reg-imm
d_b'45'cmp'45'reg'45'imm_574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_b'45'cmp'45'reg'45'imm_574 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.BlockStepAt
d_BlockStepAt_584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> ()
d_BlockStepAt_584 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.BlockStep
d_BlockStep_600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> ()
d_BlockStep_600 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-mov-rr
d_block'45'step'45'mov'45'rr_618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'rr_618 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8
                                 ~v9 ~v10 ~v11 ~v12 ~v13 v14
  = du_block'45'step'45'mov'45'rr_618 v5 v7 v8 v14
du_block'45'step'45'mov'45'rr_618 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'rr_618 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_660 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
         ~v14
  = du_dc_650 v9
du_dc_650 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_650 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_652 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_654 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_656 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_660 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14
  = du_post_660 v5 v7 v8
du_post_660 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_660 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         v1
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_662 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_664 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq-len
d_exec'45'eq'45'len_666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq'45'len_666 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_670 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-mov-to-output
d_block'45'step'45'mov'45'to'45'output_688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'to'45'output_688 ~v0 ~v1 ~v2 ~v3 ~v4 v5
                                           v6 ~v7 ~v8
  = du_block'45'step'45'mov'45'to'45'output_688 v5 v6
du_block'45'step'45'mov'45'to'45'output_688 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'to'45'output_688 v0 v1
  = coe
      du_block'45'step'45'mov'45'rr_618 (coe v0)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'to'45'output_632
         (coe d_dataCorr_524 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-mov-to-input
d_block'45'step'45'mov'45'to'45'input_712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'to'45'input_712 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
                                          ~v7 ~v8
  = du_block'45'step'45'mov'45'to'45'input_712 v5 v6
du_block'45'step'45'mov'45'to'45'input_712 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'to'45'input_712 v0 v1
  = coe
      du_block'45'step'45'mov'45'rr_618 (coe v0)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'to'45'input_648
         (coe d_dataCorr_524 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-mov-input2-to-output
d_block'45'step'45'mov'45'input2'45'to'45'output_736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'input2'45'to'45'output_736 ~v0 ~v1 ~v2
                                                     ~v3 ~v4 v5 v6 ~v7 ~v8
  = du_block'45'step'45'mov'45'input2'45'to'45'output_736 v5 v6
du_block'45'step'45'mov'45'input2'45'to'45'output_736 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'input2'45'to'45'output_736 v0 v1
  = coe
      du_block'45'step'45'mov'45'rr_618 (coe v0)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsi_18)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'input2'45'to'45'output_664
         (coe d_dataCorr_524 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-mov-output-to-input2
d_block'45'step'45'mov'45'output'45'to'45'input2_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'output'45'to'45'input2_760 ~v0 ~v1 ~v2
                                                     ~v3 ~v4 v5 v6 ~v7 ~v8
  = du_block'45'step'45'mov'45'output'45'to'45'input2_760 v5 v6
du_block'45'step'45'mov'45'output'45'to'45'input2_760 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'output'45'to'45'input2_760 v0 v1
  = coe
      du_block'45'step'45'mov'45'rr_618 (coe v0)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsi_18)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'mov'45'output'45'to'45'input2_680
         (coe d_dataCorr_524 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-mov-ri
d_block'45'step'45'mov'45'ri_790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'mov'45'ri_790 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8
                                 ~v9 ~v10 ~v11 ~v12 ~v13 v14
  = du_block'45'step'45'mov'45'ri_790 v5 v7 v8 v14
du_block'45'step'45'mov'45'ri_790 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'mov'45'ri_790 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_832 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_822 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
         ~v14
  = du_dc_822 v9
du_dc_822 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_822 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_824 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_826 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_828 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_832 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14
  = du_post_832 v5 v7 v8
du_post_832 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_832 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         v1 v2)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_834 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_836 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq-len
d_exec'45'eq'45'len_838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq'45'len_838 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_842 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-load-tag-lit
d_block'45'step'45'load'45'tag'45'lit_862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'tag'45'lit_862 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
                                          v7 ~v8 ~v9
  = du_block'45'step'45'load'45'tag'45'lit_862 v5 v6 v7
du_block'45'step'45'load'45'tag'45'lit_862 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'tag'45'lit_862 v0 v1 v2
  = coe
      du_block'45'step'45'mov'45'ri_790 (coe v0)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10) (coe v1)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'tag'45'lit_698
         (coe d_dataCorr_524 (coe v2)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-scratch-one
d_block'45'step'45'scratch'45'one_888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'scratch'45'one_888 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7
                                      ~v8
  = du_block'45'step'45'scratch'45'one_888 v5 v6
du_block'45'step'45'scratch'45'one_888 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'one_888 v0 v1
  = coe
      du_block'45'step'45'mov'45'ri_790 (coe v0)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12)
      (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'one_716
         (coe d_dataCorr_524 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-scratch-zero
d_block'45'step'45'scratch'45'zero_912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'scratch'45'zero_912 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
                                       ~v7 ~v8
  = du_block'45'step'45'scratch'45'zero_912 v5 v6
du_block'45'step'45'scratch'45'zero_912 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'zero_912 v0 v1
  = coe
      du_block'45'step'45'mov'45'ri_790 (coe v0)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'zero_732
         (coe d_dataCorr_524 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-count-zero
d_block'45'step'45'count'45'zero_936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'count'45'zero_936 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7
                                     ~v8
  = du_block'45'step'45'count'45'zero_936 v5 v6
du_block'45'step'45'count'45'zero_936 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'count'45'zero_936 v0 v1
  = coe
      du_block'45'step'45'mov'45'ri_790 (coe v0)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'count'45'zero_748
         (coe d_dataCorr_524 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-scratch-load-count
d_block'45'step'45'scratch'45'load'45'count_960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'scratch'45'load'45'count_960 ~v0 ~v1 ~v2 ~v3 ~v4
                                                v5 v6 ~v7 ~v8
  = du_block'45'step'45'scratch'45'load'45'count_960 v5 v6
du_block'45'step'45'scratch'45'load'45'count_960 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'load'45'count_960 v0 v1
  = coe
      du_block'45'step'45'mov'45'rr_618 (coe v0)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12)
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'load'45'count_764
         (coe d_dataCorr_524 (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-c-label
d_block'45'step'45'c'45'label_986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'label_986 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8
                                  ~v9
  = du_block'45'step'45'c'45'label_986 v5 v7
du_block'45'step'45'c'45'label_986 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'label_986 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1016 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (d_dataCorr_524 (coe v1))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1008 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 = du_dc_1008 v7
du_dc_1008 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1008 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1010 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1012 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1014 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1016 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_post_1016 v5
du_post_1016 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1016 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1018 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1020 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1022 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-worklist-init
d_block'45'step'45'worklist'45'init_1036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'worklist'45'init_1036 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
                                         v7 ~v8 ~v9
  = du_block'45'step'45'worklist'45'init_1036 v5 v7
du_block'45'step'45'worklist'45'init_1036 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'worklist'45'init_1036 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_1058 (coe v1))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1058 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 = du_dc_1058 v7
du_dc_1058 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1058 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-worklist-check
d_block'45'step'45'worklist'45'check_1070 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'worklist'45'check_1070 ~v0 ~v1 ~v2 ~v3 ~v4 v5
                                          ~v6 v7 ~v8 ~v9
  = du_block'45'step'45'worklist'45'check_1070 v5 v7
du_block'45'step'45'worklist'45'check_1070 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'worklist'45'check_1070 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_1092 (coe v1))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1092 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 = du_dc_1092 v7
du_dc_1092 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1092 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-reclaim-to
d_block'45'step'45'reclaim'45'to_1104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'reclaim'45'to_1104 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
                                      ~v8 ~v9
  = du_block'45'step'45'reclaim'45'to_1104 v5 v7
du_block'45'step'45'reclaim'45'to_1104 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'reclaim'45'to_1104 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_1126 (coe v1))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 = du_dc_1126 v7
du_dc_1126 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1126 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-c-jmp
d_block'45'step'45'c'45'jmp_1140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'jmp_1140 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 v8
                                 ~v9 ~v10 ~v11
  = du_block'45'step'45'c'45'jmp_1140 v3 v5 v7 v8
du_block'45'step'45'c'45'jmp_1140 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'jmp_1140 v0 v1 v2 v3
  = coe du_block'45'step_1182 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_dc_1166 v8
du_dc_1166 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1166 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1168 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1170 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1172 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fl-x86
d_fl'45'x86_1174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'x86_1174 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1176 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_post_1176 v3 v5 v7
du_post_1176 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1176 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition.du_x86'45'off_160
         (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1178 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1180 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.block-step
d_block'45'step_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step_1182 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 ~v9 ~v10 ~v11
  = du_block'45'step_1182 v3 v5 v7 v8
du_block'45'step_1182 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step_1182 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1176 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_1166 (coe v3))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-load-indirect
d_block'45'step'45'load'45'indirect_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'indirect_1200 v0 ~v1 v2 ~v3 ~v4 v5 ~v6
                                         v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_block'45'step'45'load'45'indirect_1200 v0 v2 v5 v7 v8
du_block'45'step'45'load'45'indirect_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'indirect_1200 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1242 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect_848
               (coe du_dc_1230 (coe v4)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13
  = du_dc_1230 v8
du_dc_1230 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1230 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1232 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1234 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1236 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rdi-val
d_rdi'45'val_1238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_1238 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_1240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_1240 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1242 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_post_1242 v0 v2 v5 v7
du_post_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1242 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v2))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
            v0 v1 v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1244 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1246 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1248 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-load-indirect-suc
d_block'45'step'45'load'45'indirect'45'suc_1264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'indirect'45'suc_1264 v0 ~v1 v2 ~v3 ~v4
                                                v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_block'45'step'45'load'45'indirect'45'suc_1264 v0 v2 v5 v7 v8
du_block'45'step'45'load'45'indirect'45'suc_1264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'indirect'45'suc_1264 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1310 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc_798
               (coe du_dc_1294 (coe v4)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13
  = du_dc_1294 v8
du_dc_1294 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1294 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1296 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1298 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1300 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rdi-val
d_rdi'45'val_1302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_1302 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.addr-eq
d_addr'45'eq_1304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_1304 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_1308 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1310 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_post_1310 v0 v2 v5 v7
du_post_1310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1310 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v2))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
            v0 v1 v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1312 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1314 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1316 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-load-from-slot
d_block'45'step'45'load'45'from'45'slot_1332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'from'45'slot_1332 v0 ~v1 v2 ~v3 ~v4 v5
                                             ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12
  = du_block'45'step'45'load'45'from'45'slot_1332 v0 v2 v5 v7 v8
du_block'45'step'45'load'45'from'45'slot_1332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'from'45'slot_1332 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1370 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'from'45'slot_898
               (coe du_dc_1360 (coe v4)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
  = du_dc_1360 v8
du_dc_1360 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1360 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1362 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1364 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1366 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_1368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_1368 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1370 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_post_1370 v0 v2 v5 v7
du_post_1370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1370 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v2))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
            v0 v1 v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1372 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1374 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1376 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-restore-input
d_block'45'step'45'restore'45'input_1392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'restore'45'input_1392 v0 ~v1 v2 ~v3 ~v4 v5 ~v6
                                         v7 v8 ~v9 ~v10 ~v11 ~v12
  = du_block'45'step'45'restore'45'input_1392 v0 v2 v5 v7 v8
du_block'45'step'45'restore'45'input_1392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'restore'45'input_1392 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1430 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'restore'45'input_1592
               (coe du_dc_1420 (coe v4)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
  = du_dc_1420 v8
du_dc_1420 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1420 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1422 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1424 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1426 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_1428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_1428 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1430 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_post_1430 v0 v2 v5 v7
du_post_1430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1430 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v2))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
            v0 v1 v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1432 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1434 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1436 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-alloc-stack
d_block'45'step'45'alloc'45'stack_1460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'alloc'45'stack_1460 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                       ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_block'45'step'45'alloc'45'stack_1460 v0 v4 v5 v6 v7 v15
du_block'45'step'45'alloc'45'stack_1460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'alloc'45'stack_1460 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1506 (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               du_dataPost_1512 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16
  = du_dc_1496 v7
du_dc_1496 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1496 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1498 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1500 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1502 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.newFlags
d_newFlags_1504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198
d_newFlags_1504 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16
  = du_newFlags_1504 v5 v6
du_newFlags_1504 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198
du_newFlags_1504 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.du_updateFlags_300
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82
            (coe v1)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1506 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16
  = du_post_1506 v5 v6
du_post_1506 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1506 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
            (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82
               (coe v1))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe du_newFlags_1504 (coe v0) (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1508 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1510 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_1512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_1512 v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
                ~v13 ~v14 v15 ~v16
  = du_dataPost_1512 v0 v4 v6 v7 v15
du_dataPost_1512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_1512 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'alloc'45'stack_1916
      (coe v0) (coe v2) (coe v1) (coe du_dc_1496 (coe v3)) (coe v4)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1514 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-dealloc-stack
d_block'45'step'45'dealloc'45'stack_1528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'dealloc'45'stack_1528 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                         ~v8 ~v9 ~v10
  = du_block'45'step'45'dealloc'45'stack_1528 v0 v4 v5 v6 v7
du_block'45'step'45'dealloc'45'stack_1528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'dealloc'45'stack_1528 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1562 (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe du_dataPost_1568 (coe v0) (coe v1) (coe v2) (coe v4))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1552 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_dc_1552 v7
du_dc_1552 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1552 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1554 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1556 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1558 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.newFlags
d_newFlags_1560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198
d_newFlags_1560 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_newFlags_1560 v5 v6
du_newFlags_1560 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_198
du_newFlags_1560 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.du_updateFlags_300
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1562 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_post_1562 v5 v6
du_post_1562 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1562 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
         (addInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe du_newFlags_1560 (coe v0) (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1564 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1566 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_1568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_1568 v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_dataPost_1568 v0 v4 v5 v7
du_dataPost_1568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_1568 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'dealloc'45'stack_1980
      (coe v0) (coe v1) (coe v2) (coe du_dc_1552 (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1570 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-load-const
d_block'45'step'45'load'45'const_1584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'const_1584 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
                                      ~v8 ~v9
  = du_block'45'step'45'load'45'const_1584 v5 v6 v7
du_block'45'step'45'load'45'const_1584 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'const_1584 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1614 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'const_2016
               (coe du_dc_1606 (coe v2)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 = du_dc_1606 v7
du_dc_1606 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1606 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1608 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1610 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1612 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1614 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9
  = du_post_1614 v5 v6
du_post_1614 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1614 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10) v1)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1616 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1618 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1620 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-load-const-float
d_block'45'step'45'load'45'const'45'float_1634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'const'45'float_1634 ~v0 ~v1 ~v2 ~v3 ~v4
                                               v5 v6 v7 ~v8 ~v9
  = du_block'45'step'45'load'45'const'45'float_1634 v5 v6 v7
du_block'45'step'45'load'45'const'45'float_1634 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'const'45'float_1634 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1664 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'const'45'float_2036
               (coe du_dc_1656 (coe v2)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 = du_dc_1656 v7
du_dc_1656 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1656 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1658 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1660 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1662 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1664 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9
  = du_post_1664 v5 v6
du_post_1664 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1664 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (MAlonzo.Code.Once.Semantics.FloatBits.d_float'45'bits_6 (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1666 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1668 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1670 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-load-code-addr
d_block'45'step'45'load'45'code'45'addr_1684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'code'45'addr_1684 ~v0 ~v1 ~v2 ~v3 ~v4 v5
                                             v6 v7 ~v8 ~v9
  = du_block'45'step'45'load'45'code'45'addr_1684 v5 v6 v7
du_block'45'step'45'load'45'code'45'addr_1684 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'code'45'addr_1684 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1714 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'code'45'addr_2056
               (coe du_dc_1706 (coe v2)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 = du_dc_1706 v7
du_dc_1706 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1706 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1708 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1710 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1712 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1714 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9
  = du_post_1714 v5 v6
du_post_1714 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1714 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_effectiveAddr_250
            (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'label_18
               (coe v1))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1716 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1718 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1720 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-save-closure-reg
d_block'45'step'45'save'45'closure'45'reg_1732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'save'45'closure'45'reg_1732 ~v0 ~v1 ~v2 ~v3 ~v4
                                               v5 v6 ~v7 ~v8
  = du_block'45'step'45'save'45'closure'45'reg_1732 v5 v6
du_block'45'step'45'save'45'closure'45'reg_1732 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'save'45'closure'45'reg_1732 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1760 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_1752 (coe v1))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 = du_dc_1752 v6
du_dc_1752 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1752 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1754 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1756 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1758 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1760 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 = du_post_1760 v5
du_post_1760 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1760 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34)
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1762 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1764 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1766 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-worklist-push
d_block'45'step'45'worklist'45'push_1782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'worklist'45'push_1782 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
                                         v7 ~v8 ~v9 ~v10 ~v11
  = du_block'45'step'45'worklist'45'push_1782 v4 v5 v6 v7
du_block'45'step'45'worklist'45'push_1782 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'worklist'45'push_1782 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1816 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dataPost_1826 (coe v0) (coe v3))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1808 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_dc_1808 v7
du_dc_1808 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1808 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1810 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1812 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1814 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1816 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_post_1816 v5 v6
du_post_1816 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1816 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_effectiveAddr_250
            (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
                  (coe v1))))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1818 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1820 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-eq
d_post'45'eq_1822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_post'45'eq_1822 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_1826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_1826 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_dataPost_1826 v4 v7
du_dataPost_1826 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_1826 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'at'45'slot_1864
      (coe v0) (coe du_dc_1808 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1828 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-worklist-pop
d_block'45'step'45'worklist'45'pop_1844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'worklist'45'pop_1844 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7
                                        v8 ~v9 ~v10 ~v11 ~v12
  = du_block'45'step'45'worklist'45'pop_1844 v0 v2 v5 v7 v8
du_block'45'step'45'worklist'45'pop_1844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'worklist'45'pop_1844 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1882 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'from'45'slot_898
               (coe du_dc_1872 (coe v4)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1872 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
  = du_dc_1872 v8
du_dc_1872 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1872 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1874 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1876 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1878 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_1880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_1880 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1882 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_post_1882 v0 v2 v5 v7
du_post_1882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1882 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v2))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
            v0 v1 v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1884 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1886 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1888 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-store-indirect
d_block'45'step'45'store'45'indirect_1902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'store'45'indirect_1902 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
                                          v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_block'45'step'45'store'45'indirect_1902 v4 v5 v6 v7 v11
du_block'45'step'45'store'45'indirect_1902 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'store'45'indirect_1902 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_1940 (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe du_dataPost_1950 (coe v0) (coe v2) (coe v3) (coe v4))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1930 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_dc_1930 v7
du_dc_1930 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1930 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1932 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1934 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_1936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_1936 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rdi-val
d_rdi'45'val_1938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_1938 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_1940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_1940 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_post_1940 v5
du_post_1940 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_1940 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_effectiveAddr_250
            (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_12
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_1942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_1942 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_1944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_1944 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-eq
d_post'45'eq_1946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_post'45'eq_1946 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_1950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_1950 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_dataPost_1950 v4 v6 v7 v11
du_dataPost_1950 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_1950 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect_1494
      (coe v1) (coe v0) (coe du_dc_1930 (coe v2)) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_1952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_1952 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-store-indirect-suc
d_block'45'step'45'store'45'indirect'45'suc_1966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'store'45'indirect'45'suc_1966 ~v0 ~v1 ~v2 ~v3 v4
                                                 v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_block'45'step'45'store'45'indirect'45'suc_1966 v4 v5 v6 v7 v11
du_block'45'step'45'store'45'indirect'45'suc_1966 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'store'45'indirect'45'suc_1966 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_2008 (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe du_dataPost_2018 (coe v0) (coe v2) (coe v3) (coe v4))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_1994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_1994 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_dc_1994 v7
du_dc_1994 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_1994 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_1996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_1996 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_1998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_1998 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_2000 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_2000 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rdi-val
d_rdi'45'val_2002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_2002 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.addr-val
d_addr'45'val_2004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'val_2004 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_2008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_2008 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_post_2008 v5
du_post_2008 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_2008 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_effectiveAddr_250
            (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_2010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_2010 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2012 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-eq
d_post'45'eq_2014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_post'45'eq_2014 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_2018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_2018 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_dataPost_2018 v4 v6 v7 v11
du_dataPost_2018 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_2018 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc_1542
      (coe v1) (coe v0) (coe du_dc_1994 (coe v2)) (coe v3)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_2020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_2020 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-store-at-slot
d_block'45'step'45'store'45'at'45'slot_2036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'store'45'at'45'slot_2036 ~v0 ~v1 ~v2 ~v3 v4 v5
                                            v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_block'45'step'45'store'45'at'45'slot_2036 v4 v5 v6 v7
du_block'45'step'45'store'45'at'45'slot_2036 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'store'45'at'45'slot_2036 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_2070 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dataPost_2080 (coe v0) (coe v3))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2062 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_dc_2062 v7
du_dc_2062 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2062 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2064 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2066 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_2068 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_2068 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_2070 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_2070 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_post_2070 v5 v6
du_post_2070 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_2070 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_effectiveAddr_250
            (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
                  (coe v1))))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_2072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_2072 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2074 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-eq
d_post'45'eq_2076 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_post'45'eq_2076 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_2080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_2080 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_dataPost_2080 v4 v7
du_dataPost_2080 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_2080 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'at'45'slot_1864
      (coe v0) (coe du_dc_2062 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_2082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_2082 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-count-inc
d_block'45'step'45'count'45'inc_2096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'count'45'inc_2096 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
                                     ~v8 ~v9 ~v10
  = du_block'45'step'45'count'45'inc_2096 v5 v7
du_block'45'step'45'count'45'inc_2096 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'count'45'inc_2096 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_2128 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'count'45'inc_2114
               (coe du_dc_2120 (coe v1)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_dc_2120 v7
du_dc_2120 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2120 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2122 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2124 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_2126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_2126 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_2128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_2128 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_post_2128 v5
du_post_2128 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_2128 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38)
         (addInt
            (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.du_updateFlags_300
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38))))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_2130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_2130 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2132 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_2134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_2134 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-scratch-dec
d_block'45'step'45'scratch'45'dec_2148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'scratch'45'dec_2148 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
                                       v7 ~v8 ~v9 ~v10
  = du_block'45'step'45'scratch'45'dec_2148 v5 v7
du_block'45'step'45'scratch'45'dec_2148 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'scratch'45'dec_2148 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_2180 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'reg'45'scratch'45'dec_2142
               (coe du_dc_2172 (coe v1)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_dc_2172 v7
du_dc_2172 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2172 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2174 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2176 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_2178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_2178 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_2180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_2180 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_post_2180 v5
du_post_2180 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_2180 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12)
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (1 :: Integer)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.du_updateFlags_300
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (1 :: Integer)))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_2182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_2182 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2184 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_2186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_2186 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-c-branch-scratch-zero
d_block'45'step'45'c'45'branch'45'scratch'45'zero_2204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'scratch'45'zero_2204 ~v0 ~v1 ~v2
                                                       v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
  = du_block'45'step'45'c'45'branch'45'scratch'45'zero_2204
      v3 v5 v7 v8 v9
du_block'45'step'45'c'45'branch'45'scratch'45'zero_2204 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'scratch'45'zero_2204 v0 v1 v2 v3
                                                        v4
  = case coe v2 of
      0 -> coe du_result_2262 (coe v0) (coe v1) (coe v3) (coe v4)
      _ -> coe du_result_2332 (coe v1) (coe v4)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
  = du_dc_2232 v8
du_dc_2232 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2232 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2234 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2236 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-cmp
d_fetch'45'cmp_2238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'cmp_2238 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-cmp
d_post'45'cmp_2240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'cmp_2240 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12
  = du_post'45'cmp_2240 v5
du_post'45'cmp_2240 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'cmp_2240 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe
            eqInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-cmp
d_step'45'cmp_2242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp_2242 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rbx-val
d_rbx'45'val_2244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'val_2244 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-je
d_fetch'45'je_2246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'je_2246 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.zf-true
d_zf'45'true_2250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zf'45'true_2250 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fl-x86
d_fl'45'x86_2254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'x86_2254 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-je
d_post'45'je_2256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'je_2256 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
                  ~v12
  = du_post'45'je_2256 v3 v5 v7
du_post'45'je_2256 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'je_2256 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe
            eqInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v1))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v1))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition.du_x86'45'off_160
         (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-je
d_step'45'je_2258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je_2258 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2260 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.result
d_result_2262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_result_2262 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12
  = du_result_2262 v3 v5 v7 v8
du_result_2262 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_result_2262 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post'45'je_2256 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_2232 (coe v3))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
          ~v13
  = du_dc_2300 v9
du_dc_2300 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2300 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2302 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2304 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-cmp
d_fetch'45'cmp_2306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'cmp_2306 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-cmp
d_post'45'cmp_2308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'cmp_2308 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13
  = du_post'45'cmp_2308 v5
du_post'45'cmp_2308 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'cmp_2308 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe
            eqInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-cmp
d_step'45'cmp_2310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp_2310 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rbx-val
d_rbx'45'val_2312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'val_2312 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-je
d_fetch'45'je_2314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'je_2314 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.zf-false
d_zf'45'false_2318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zf'45'false_2318 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-je
d_post'45'je_2322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'je_2322 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13
  = du_post'45'je_2322 v5
du_post'45'je_2322 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'je_2322 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe
            eqInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-je
d_step'45'je_2324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je_2324 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2326 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_2328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_2328 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.result
d_result_2332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_result_2332 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
              ~v13
  = du_result_2332 v5 v9
du_result_2332 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_result_2332 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post'45'je_2322 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_2300 (coe v1))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-c-branch-tag-zero
d_block'45'step'45'c'45'branch'45'tag'45'zero_2354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'tag'45'zero_2354 ~v0 ~v1 ~v2 v3
                                                   ~v4 v5 ~v6 ~v7 v8 v9 v10 ~v11 ~v12 ~v13 ~v14 ~v15
                                                   ~v16
  = du_block'45'step'45'c'45'branch'45'tag'45'zero_2354
      v3 v5 v8 v9 v10
du_block'45'step'45'c'45'branch'45'tag'45'zero_2354 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'tag'45'zero_2354 v0 v1 v2 v3 v4
  = case coe v2 of
      0 -> coe du_result_2414 (coe v0) (coe v1) (coe v3) (coe v4)
      _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
           coe (coe du_result_2486 (coe v1) (coe v5) (coe v4))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15
  = du_dc_2388 v9
du_dc_2388 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2388 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2390 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2392 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-cmp
d_fetch'45'cmp_2394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'cmp_2394 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-cmp
d_post'45'cmp_2396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'cmp_2396 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15
  = du_post'45'cmp_2396 v5
du_post'45'cmp_2396 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'cmp_2396 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe eqInt (coe (0 :: Integer)) (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe (0 :: Integer)) (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-cmp
d_step'45'cmp_2398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp_2398 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-je
d_fetch'45'je_2400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'je_2400 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fl-x86
d_fl'45'x86_2404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'x86_2404 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-je
d_post'45'je_2406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'je_2406 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15
  = du_post'45'je_2406 v3 v5 v8
du_post'45'je_2406 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'je_2406 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe eqInt (coe (0 :: Integer)) (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe (0 :: Integer)) (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition.du_x86'45'off_160
         (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-je
d_step'45'je_2408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je_2408 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2410 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.cond-eq
d_cond'45'eq_2412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cond'45'eq_2412 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.result
d_result_2414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_result_2414 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
              ~v13 ~v14 ~v15
  = du_result_2414 v3 v5 v8 v9
du_result_2414 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_result_2414 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post'45'je_2406 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_2388 (coe v3))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16
  = du_dc_2458 v10
du_dc_2458 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2458 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2460 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2462 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-cmp
d_fetch'45'cmp_2464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'cmp_2464 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-cmp
d_post'45'cmp_2466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'cmp_2466 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16
  = du_post'45'cmp_2466 v5 v8
du_post'45'cmp_2466 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'cmp_2466 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe eqInt (coe v1) (coe (-1 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe addInt (coe (1 :: Integer)) (coe v1)) (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-cmp
d_step'45'cmp_2468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp_2468 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-je
d_fetch'45'je_2470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'je_2470 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-je
d_post'45'je_2474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'je_2474 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16
  = du_post'45'je_2474 v5 v8
du_post'45'je_2474 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'je_2474 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe eqInt (coe v1) (coe (-1 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe addInt (coe (1 :: Integer)) (coe v1)) (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-je
d_step'45'je_2476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je_2476 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2478 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.cond-eq
d_cond'45'eq_2480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cond'45'eq_2480 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_2482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_2482 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.result
d_result_2486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_result_2486 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 v10 ~v11 ~v12
              ~v13 ~v14 ~v15 ~v16
  = du_result_2486 v5 v8 v10
du_result_2486 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_result_2486 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post'45'je_2474 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_2458 (coe v2))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.load-indirect-heap-empty-stuck
d_load'45'indirect'45'heap'45'empty'45'stuck_2502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'heap'45'empty'45'stuck_2502 ~v0 ~v1 ~v2 ~v3
                                                  ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_load'45'indirect'45'heap'45'empty'45'stuck_2502
du_load'45'indirect'45'heap'45'empty'45'stuck_2502 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'heap'45'empty'45'stuck_2502
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_dc_2528 v7
du_dc_2528 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2528 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2530 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_2532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_2532 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rdi-val
d_rdi'45'val_2534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_2534 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_2536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_2536 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.stuck
d_stuck_2538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stuck_2538 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.load-indirect-stack-empty-stuck
d_load'45'indirect'45'stack'45'empty'45'stuck_2556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'stack'45'empty'45'stuck_2556 ~v0 ~v1 ~v2 ~v3
                                                   ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_load'45'indirect'45'stack'45'empty'45'stuck_2556
du_load'45'indirect'45'stack'45'empty'45'stuck_2556 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'stack'45'empty'45'stuck_2556
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13
  = du_dc_2586 v8
du_dc_2586 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2586 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2588 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_2590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_2590 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rdi-val
d_rdi'45'val_2592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_2592 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_2600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_2600 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.stuck
d_stuck_2602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stuck_2602 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.load-indirect-suc-heap-empty-stuck
d_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_2618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_2618 ~v0 ~v1
                                                         ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_2618
du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_2618 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'heap'45'empty'45'stuck_2618
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2644 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_dc_2644 v7
du_dc_2644 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2644 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2646 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_2648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_2648 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rdi-val
d_rdi'45'val_2650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_2650 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.addr-eq
d_addr'45'eq_2652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_2652 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_2656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_2656 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.stuck
d_stuck_2658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stuck_2658 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.load-indirect-suc-stack-empty-stuck
d_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_2676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_2676 ~v0 ~v1
                                                          ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                                                          ~v12 ~v13
  = du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_2676
du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_2676 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'stack'45'empty'45'stuck_2676
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13
  = du_dc_2706 v8
du_dc_2706 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2706 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2708 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_2710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_2710 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.addr-eq
d_addr'45'eq_2712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_2712 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_2724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_2724 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.stuck
d_stuck_2726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stuck_2726 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-c-branch-tag-nz
d_block'45'step'45'c'45'branch'45'tag'45'nz_2746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'tag'45'nz_2746 ~v0 ~v1 ~v2 ~v3
                                                 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_block'45'step'45'c'45'branch'45'tag'45'nz_2746 v5 v8 v9
du_block'45'step'45'c'45'branch'45'tag'45'nz_2746 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'tag'45'nz_2746 v0 v1 v2
  = coe du_result_2806 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2778 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
          ~v13 ~v14
  = du_dc_2778 v9
du_dc_2778 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2778 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2780 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2782 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-cmp
d_fetch'45'cmp_2784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'cmp_2784 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-cmp
d_post'45'cmp_2786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'cmp_2786 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14
  = du_post'45'cmp_2786 v5 v8
du_post'45'cmp_2786 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'cmp_2786 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe eqInt (coe v1) (coe (-1 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe addInt (coe (1 :: Integer)) (coe v1)) (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-cmp
d_step'45'cmp_2788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp_2788 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-je
d_fetch'45'je_2790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'je_2790 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-je
d_post'45'je_2794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'je_2794 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14
  = du_post'45'je_2794 v5 v8
du_post'45'je_2794 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'je_2794 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe eqInt (coe v1) (coe (-1 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe addInt (coe (1 :: Integer)) (coe v1)) (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-je
d_step'45'je_2796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je_2796 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2798 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.cond-eq
d_cond'45'eq_2800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cond'45'eq_2800 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_2802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_2802 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.result
d_result_2806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_result_2806 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
              ~v13 ~v14
  = du_result_2806 v5 v8 v9
du_result_2806 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_result_2806 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post'45'je_2794 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_2778 (coe v2))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-alloc-heap
d_block'45'step'45'alloc'45'heap_2834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'alloc'45'heap_2834 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                      ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_block'45'step'45'alloc'45'heap_2834 v4 v5 v6 v7
du_block'45'step'45'alloc'45'heap_2834 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'alloc'45'heap_2834 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post'45'add_2888 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dataPost_2894 (coe v0) (coe v3))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2872 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17
  = du_dc_2872 v7
du_dc_2872 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2872 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2874 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2876 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-mov
d_fetch'45'mov_2878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'mov_2878 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-mov
d_post'45'mov_2880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'mov_2880 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_post'45'mov_2880 v5
du_post'45'mov_2880 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'mov_2880 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step1
d_step1_2882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step1_2882 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-add
d_fetch'45'add_2884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'add_2884 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-add
d_post'45'add_2888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'add_2888 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_post'45'add_2888 v5 v6
du_post'45'add_2888 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'add_2888 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
            (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
               (coe v0))
            (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
            (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40)))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40)
         (addInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
                  (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                     (coe v0))
                  (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
                  (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                        (coe v0))
                     (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40)))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.du_updateFlags_300
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82 (coe v1))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
                  (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                     (coe v0))
                  (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
                  (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                        (coe v0))
                     (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40)))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40))))
      (coe
         addInt (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step2
d_step2_2890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_2890 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2892 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_2894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_2894 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_dataPost_2894 v4 v7
du_dataPost_2894 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_2894 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'alloc'45'heap_2680
      (coe v0) (coe du_dc_2872 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_2896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_2896 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-lea-slot
d_block'45'step'45'lea'45'slot_2910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'lea'45'slot_2910 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
                                    ~v8 ~v9
  = du_block'45'step'45'lea'45'slot_2910 v5 v6 v7
du_block'45'step'45'lea'45'slot_2910 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'lea'45'slot_2910 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_2940 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            C_constructor_528
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'lea'45'slot_2796
               (coe du_dc_2932 (coe v2)))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2932 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 = du_dc_2932 v7
du_dc_2932 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2932 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2934 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2936 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_2938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_2938 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_2940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_2940 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9
  = du_post_2940 v5 v6
du_post_2940 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_2940 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_effectiveAddr_250
            (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
                  (coe v1)))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_2942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_2942 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_2944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_2944 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_2946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_2946 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-c-branch-nz
d_block'45'step'45'c'45'branch'45'nz_2962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'c'45'branch'45'nz_2962 ~v0 ~v1 ~v2 ~v3 ~v4 v5
                                          ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_block'45'step'45'c'45'branch'45'nz_2962 v5 v8
du_block'45'step'45'c'45'branch'45'nz_2962 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'c'45'branch'45'nz_2962 v0 v1
  = coe du_result_3020 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_2988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_2988 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_dc_2988 v8
du_dc_2988 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_2988 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_2990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_2990 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_2992 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_2992 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-cmp
d_fetch'45'cmp_2994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'cmp_2994 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-cmp
d_post'45'cmp_2996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'cmp_2996 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_post'45'cmp_2996 v5
du_post'45'cmp_2996 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'cmp_2996 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe
            eqInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-cmp
d_step'45'cmp_2998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'cmp_2998 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rbx-val
d_rbx'45'val_3000 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rbx'45'val_3000 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-je
d_fetch'45'je_3002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'je_3002 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.zf-false
d_zf'45'false_3006 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zf'45'false_3006 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post-je
d_post'45'je_3010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post'45'je_3010 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_post'45'je_3010 v5
du_post'45'je_3010 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post'45'je_3010 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkflags_212
         (coe
            eqInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d__'60''7495'__304
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v0))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12))
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe
         addInt (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.step-je
d_step'45'je_3012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'je_3012 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_3014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_3014 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_3016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_3016 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.result
d_result_3020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_result_3020 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_result_3020 v5 v8
du_result_3020 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_result_3020 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post'45'je_3010 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dc_2988 (coe v1))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-load-indirect-stack
d_block'45'step'45'load'45'indirect'45'stack_3040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'indirect'45'stack_3040 v0 ~v1 v2 ~v3 ~v4
                                                  v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_block'45'step'45'load'45'indirect'45'stack_3040 v0 v2 v5 v8 v9
du_block'45'step'45'load'45'indirect'45'stack_3040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'indirect'45'stack_3040 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_3092 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dataPost_3098 (coe v4))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_3074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_3074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15
  = du_dc_3074 v9
du_dc_3074 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_3074 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_3076 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_3076 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_3078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_3078 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_3080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_3080 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rdi-val
d_rdi'45'val_3082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_3082 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_3090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_3090 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_3092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_3092 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15
  = du_post_3092 v0 v2 v5 v8
du_post_3092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_3092 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v2))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
            v0 v1 v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_3094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_3094 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_3096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_3096 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_3098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_3098 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15
  = du_dataPost_3098 v9
du_dataPost_3098 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_3098 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'stack_2832
      (coe du_dc_3074 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_3102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_3102 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-load-indirect-suc-stack
d_block'45'step'45'load'45'indirect'45'suc'45'stack_3120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'load'45'indirect'45'suc'45'stack_3120 v0 ~v1 v2
                                                         ~v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
                                                         ~v13 ~v14 ~v15
  = du_block'45'step'45'load'45'indirect'45'suc'45'stack_3120
      v0 v2 v5 v8 v9
du_block'45'step'45'load'45'indirect'45'suc'45'stack_3120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'load'45'indirect'45'suc'45'stack_3120 v0 v1 v2
                                                          v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_3176 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dataPost_3182 (coe v4))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_3154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_3154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15
  = du_dc_3154 v9
du_dc_3154 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_3154 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_3156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_3156 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_3158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_3158 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_3160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_3160 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.addr-eq
d_addr'45'eq_3162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_3162 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rd
d_rd_3174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd_3174 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_3176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_3176 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15
  = du_post_3176 v0 v2 v5 v8
du_post_3176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_3176 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v2))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
            v0 v1 v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v2))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_3178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_3178 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_3180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_3180 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_3182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_3182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15
  = du_dataPost_3182 v9
du_dataPost_3182 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_3182 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc'45'stack_2886
      (coe du_dc_3154 (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_3186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_3186 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-store-indirect-stack
d_block'45'step'45'store'45'indirect'45'stack_3204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'store'45'indirect'45'stack_3204 v0 ~v1 v2 ~v3 v4
                                                   v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_block'45'step'45'store'45'indirect'45'stack_3204
      v0 v2 v4 v5 v7 v8
du_block'45'step'45'store'45'indirect'45'stack_3204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'store'45'indirect'45'stack_3204 v0 v1 v2 v3 v4
                                                    v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_3258 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dataPost_3268 (coe v2) (coe v5))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_3236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_3236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14
  = du_dc_3236 v8
du_dc_3236 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_3236 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_3238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_3238 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.Out
d_Out_3240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_3240 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14
  = du_Out_3240 v4
du_Out_3240 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_3240 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_3242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_3242 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_3244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_3244 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.rdi-val
d_rdi'45'val_3246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_3246 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.i-eq'
d_i'45'eq''_3254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'45'eq''_3254 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_3258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_3258 v0 ~v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14
  = du_post_3258 v0 v2 v4 v5 v7
du_post_3258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_3258 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v3))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v3))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
               (coe v4)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
            v0 v1 (coe du_Out_3240 (coe v2))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v3))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_3260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_3260 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_3266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_3266 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_3268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_3268 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14
  = du_dataPost_3268 v4 v8
du_dataPost_3268 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_3268 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'stack_2938
      (coe v0) (coe du_dc_3236 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_3270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_3270 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation.block-step-store-indirect-suc-stack
d_block'45'step'45'store'45'indirect'45'suc'45'stack_3288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'step'45'store'45'indirect'45'suc'45'stack_3288 v0 ~v1 v2
                                                          ~v3 v4 v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12
                                                          ~v13 ~v14
  = du_block'45'step'45'store'45'indirect'45'suc'45'stack_3288
      v0 v2 v4 v5 v7 v8
du_block'45'step'45'store'45'indirect'45'suc'45'stack_3288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  T_CompiledCorr_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_block'45'step'45'store'45'indirect'45'suc'45'stack_3288 v0 v1 v2
                                                           v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_post_3346 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe C_constructor_528 (coe du_dataPost_3356 (coe v2) (coe v5))))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dc
d_dc_3320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dc_3320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14
  = du_dc_3320 v8
du_dc_3320 ::
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dc_3320 v0 = coe d_dataCorr_524 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.po
d_po_3322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_po_3322 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.Out
d_Out_3324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_3324 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14
  = du_Out_3324 v4
du_Out_3324 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_3324 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.halt-s
d_halt'45's_3326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45's_3326 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.fetch-x86
d_fetch'45'x86_3328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'x86_3328 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.addr-eq
d_addr'45'eq_3330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_3330 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.i-eq'
d_i'45'eq''_3342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'45'eq''_3342 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.post
d_post_3346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_post_3346 v0 ~v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14
  = du_post_3346 v0 v2 v4 v5 v7
du_post_3346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
du_post_3346 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v3))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
            (coe v3))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
               (coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                  (coe v3))
               (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_slot'45'to'45'disp_10
               (coe addInt (coe (1 :: Integer)) (coe v4))))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_enc'45'sv_312
            v0 v1 (coe du_Out_3324 (coe v2))))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v3))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v3)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v3))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.snh
d_snh_3348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snh_3348 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.exec-eq
d_exec'45'eq_3354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'eq_3354 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.dataPost
d_dataPost_3356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
d_dataPost_3356 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14
  = du_dataPost_3356 v4 v8
du_dataPost_3356 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_FlatCorr_368
du_dataPost_3356 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc'45'stack_2994
      (coe v0) (coe du_dc_3320 (coe v1))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation._.pco'
d_pco''_3358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence.T_HeapView_218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  AgdaAny ->
  Integer ->
  T_CompiledCorr_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pco''_3358 = erased
