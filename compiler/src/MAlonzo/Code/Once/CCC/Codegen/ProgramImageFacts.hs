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

module MAlonzo.Code.Once.CCC.Codegen.ProgramImageFacts where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.Codegen.AllocMin
import qualified MAlonzo.Code.Once.CCC.Codegen.FrameFreeTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.LabelRange
import qualified MAlonzo.Code.Once.CCC.Codegen.LabelScope
import qualified MAlonzo.Code.Once.CCC.Codegen.LabelSeg
import qualified MAlonzo.Code.Once.CCC.Codegen.ProgramImage
import qualified MAlonzo.Code.Once.CCC.Codegen.ShapeTable
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotBudget
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotSeg
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy

-- Once.CCC.Codegen.ProgramImageFacts._.AllocMinI
d_AllocMinI_12 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 -> ()
d_AllocMinI_12 = erased
-- Once.CCC.Codegen.ProgramImageFacts.fns-next
d_fns'45'next_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> Integer
d_fns'45'next_14 ~v0 v1 v2 = du_fns'45'next_14 v1 v2
du_fns'45'next_14 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> Integer
du_fns'45'next_14 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             du_fns'45'next_14
             (coe
                MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                (coe v2))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImageFacts.fn-mono
d_fn'45'mono_28 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fn'45'mono_28 ~v0 v1 v2 = du_fn'45'mono_28 v1 v2
du_fn'45'mono_28 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fn'45'mono_28 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelRange.d_label'45'mono_150
      (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))
      (coe (0 :: Integer)) (coe v0)
-- Once.CCC.Codegen.ProgramImageFacts.fns-mono
d_fns'45'mono_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fns'45'mono_38 ~v0 v1 v2 = du_fns'45'mono_38 v1 v2
du_fns'45'mono_38 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fns'45'mono_38 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe du_fn'45'mono_28 (coe v0) (coe v2))
             (coe
                du_fns'45'mono_38
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                   (coe v2))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImageFacts.fns-frame-free
d_fns'45'frame'45'free_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fns'45'frame'45'free_52 ~v0 v1 v2
  = du_fns'45'frame'45'free_52 v1 v2
du_fns'45'frame'45'free_52 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fns'45'frame'45'free_52 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2304
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2224
                      (coe
                         MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2)))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_854
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe v0)
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))))
                (let v4
                       = MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2) in
                 coe
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_882
                      (coe v4)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (MAlonzo.Code.Once.CCC.Codegen.FrameFreeTrace.d_ir'45'to'45'trace'45'lab'45'frame'45'free_984
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_heap'45'moded_958
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))
                   (coe v0)))
             (coe
                du_fns'45'frame'45'free_52
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                   (coe v2))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImageFacts.image-frame-free
d_image'45'frame'45'free_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_image'45'frame'45'free_66 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_806
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.FrameFreeTrace.d_ir'45'to'45'trace'45'frame'45'free_968
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_heap'45'moded_958
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)))
      (coe
         du_fns'45'frame'45'free_52
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_892
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
            (coe v2))
         (coe v1))
-- Once.CCC.Codegen.ProgramImageFacts.fns-alloc-min
d_fns'45'alloc'45'min_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fns'45'alloc'45'min_76 ~v0 v1 v2
  = du_fns'45'alloc'45'min_76 v1 v2
du_fns'45'alloc'45'min_76 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fns'45'alloc'45'min_76 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2304
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2224
                      (coe
                         MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2)))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_854
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe v0)
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))))
                (let v4
                       = MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2) in
                 coe
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_882
                      (coe v4)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (MAlonzo.Code.Once.CCC.Codegen.AllocMin.d_ir'45'to'45'trace'45'lab'45'alloc'45'min_886
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                   (coe v0)))
             (coe
                du_fns'45'alloc'45'min_76
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                   (coe v2))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImageFacts.image-alloc-min
d_image'45'alloc'45'min_90 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_image'45'alloc'45'min_90 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_806
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.AllocMin.d_ir'45'to'45'trace'45'alloc'45'min_874
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))
      (coe
         du_fns'45'alloc'45'min_76
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_892
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
            (coe v2))
         (coe v1))
-- Once.CCC.Codegen.ProgramImageFacts.fns-slots
d_fns'45'slots_102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_222
d_fns'45'slots_102 ~v0 v1 v2 v3 = du_fns'45'slots_102 v1 v2 v3
du_fns'45'slots_102 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_222
du_fns'45'slots_102 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C_'91''93'_226
      (:) v3 v4
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45''43''43'_242
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2304
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2224
                      (coe
                         MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3)))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_854
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                         (coe v1)
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3)))))
                (let v5
                       = MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3) in
                 coe
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_882
                      (coe v5)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                      (coe v1)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3)))))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C__'8759'__234
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (MAlonzo.Code.Once.CCC.Codegen.SlotBudget.d_ir'45'slots'45'below'45'under'45'lab_1826
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3))
                   (coe v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                du_fns'45'slots_102 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v1)
                   (coe v3))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImageFacts.image-slots
d_image'45'slots_122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_222
d_image'45'slots_122 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45''43''43'_242
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_806
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotBudget.d_ir'45'slots'45'below'45'under_1862
         v0 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v2
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         du_fns'45'slots_102
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_824
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_892
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
            (coe v2))
         (coe v1))
-- Once.CCC.Codegen.ProgramImageFacts.fn-labels
d_fn'45'labels_134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fn'45'labels_134 ~v0 v1 v2 = du_fn'45'labels_134 v1 v2
du_fn'45'labels_134 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fn'45'labels_134 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.LabelSeg.du_li'45'none_54)
      (MAlonzo.Code.Once.CCC.Codegen.LabelScope.d_linked'45'labels'45'lab_3460
         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))
         (coe v0))
-- Once.CCC.Codegen.ProgramImageFacts.fn-agree
d_fn'45'agree_144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegState_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fn'45'agree_144 = erased
-- Once.CCC.Codegen.ProgramImageFacts.fns-labels
d_fns'45'labels_154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fns'45'labels_154 ~v0 v1 v2 = du_fns'45'labels_154 v1 v2
du_fns'45'labels_154 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fns'45'labels_154 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'image_8 (coe v0)
                (coe v2))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.LabelSeg.du_ls'45'weaken_144
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'image_8 (coe v0)
                   (coe v2))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
                (coe
                   du_fns'45'mono_38
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                      (coe v2))
                   (coe v3))
                (coe du_fn'45'labels_134 (coe v0) (coe v2)))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.LabelSeg.du_ls'45'weaken_144
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                      (coe v2))
                   (coe v3))
                (coe du_fn'45'mono_28 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                   (coe
                      du_fns'45'next_14
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                         (coe v2))
                      (coe v3)))
                (coe
                   du_fns'45'labels_154
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                      (coe v2))
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImageFacts.fns-agree
d_fns'45'agree_168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegState_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fns'45'agree_168 = erased
-- Once.CCC.Codegen.ProgramImageFacts.image-agree
d_image'45'agree_182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegState_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_image'45'agree_182 = erased
-- Once.CCC.Codegen.ProgramImageFacts._.L
d_L_192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_L_192 v0 ~v1 v2 = du_L_192 v0 v2
du_L_192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_L_192 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_892
      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
      (coe v1)
-- Once.CCC.Codegen.ProgramImageFacts._._.fetch
d_fetch_202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236
d_fetch_202 ~v0 ~v1 = du_fetch_202
du_fetch_202 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236
du_fetch_202 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.CCC.Codegen.ProgramImageFacts._._.find-label
d_find'45'label_204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_204 ~v0 v1 = du_find'45'label_204 v1
du_find'45'label_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_204 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.CCC.Codegen.ProgramImageFacts._.fetch≡at
d_fetch'8801'at_212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'8801'at_212 = erased
-- Once.CCC.Codegen.ProgramImageFacts._.image-jump-in-segment
d_image'45'jump'45'in'45'segment_236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_SegState_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_image'45'jump'45'in'45'segment_236 = erased
