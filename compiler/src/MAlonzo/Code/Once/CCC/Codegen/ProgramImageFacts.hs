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
import qualified MAlonzo.Code.Once.CCC.Machine.FrameFree
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy

-- Once.CCC.Codegen.ProgramImageFacts._.AllocMinI
d_AllocMinI_12 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> ()
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
      MAlonzo.Code.Once.CCC.Codegen.LabelRange.d_label'45'mono_160
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
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236
                      (coe
                         MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2)))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_908
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe v0)
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))))
                (let v4
                       = MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2) in
                 coe
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_936
                      (coe v4)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (MAlonzo.Code.Once.CCC.Codegen.FrameFreeTrace.d_ir'45'to'45'trace'45'lab'45'frame'45'free_1020
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_heap'45'moded_988
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
-- Once.CCC.Codegen.ProgramImageFacts.body-frame-free
d_body'45'frame'45'free_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_body'45'frame'45'free_66 v0 v1 v2
  = coe
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
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_854 v0
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v2))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.FrameFreeTrace.du_ir'45'to'45'trace'45'top'45'frame'45'free_1038
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ShapeTable.d_heap'45'moded_988
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)))
      (coe
         du_fns'45'frame'45'free_52
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_946
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
               (coe v2)))
         (coe v1))
-- Once.CCC.Codegen.ProgramImageFacts.image-frame-free
d_image'45'frame'45'free_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_image'45'frame'45'free_76 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         du_All'45'map'8242'_88
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_image'45'body_36
            (coe v0)
            (coe
               MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
               (coe v2)))
         (coe d_body'45'frame'45'free_66 (coe v0) (coe v1) (coe v2)))
-- Once.CCC.Codegen.ProgramImageFacts._.All-map′
d_All'45'map'8242'_88 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_All'45'map'8242'_88 ~v0 ~v1 ~v2 v3 v4
  = du_All'45'map'8242'_88 v3 v4
du_All'45'map'8242'_88 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_All'45'map'8242'_88 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v1
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (MAlonzo.Code.Once.CCC.Machine.FrameFree.d_emittable'45'image_30
                       (coe v6) (coe v4))
                    (coe du_All'45'map'8242'_88 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImageFacts.fns-alloc-min
d_fns'45'alloc'45'min_100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fns'45'alloc'45'min_100 ~v0 v1 v2
  = du_fns'45'alloc'45'min_100 v1 v2
du_fns'45'alloc'45'min_100 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fns'45'alloc'45'min_100 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
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
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2)))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_908
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe v0)
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))))
                (let v4
                       = MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2) in
                 coe
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_936
                      (coe v4)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (MAlonzo.Code.Once.CCC.Codegen.AllocMin.d_ir'45'to'45'trace'45'lab'45'alloc'45'min_922
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                   (coe v0)))
             (coe
                du_fns'45'alloc'45'min_100
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                   (coe v2))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImageFacts.image-alloc-min
d_image'45'alloc'45'min_114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_image'45'alloc'45'min_114 v0 v1 v2
  = coe
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
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_854 v0
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v2))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.AllocMin.du_ir'45'to'45'trace'45'top'45'alloc'45'min_936
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))
         (coe
            du_fns'45'alloc'45'min_100
            (coe
               addInt (coe (1 :: Integer))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_946
                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
                  (coe v2)))
            (coe v1)))
-- Once.CCC.Codegen.ProgramImageFacts.fns-slots
d_fns'45'slots_128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [Integer] ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
d_fns'45'slots_128 ~v0 v1 v2 v3 v4
  = du_fns'45'slots_128 v1 v2 v3 v4
du_fns'45'slots_128 ::
  Integer ->
  [Integer] ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
du_fns'45'slots_128 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C_'91''93'_228
      (:) v4 v5
        -> coe
             MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45''43''43'_244
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236
                      (coe
                         MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v4)))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_908
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v4))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4))
                         (coe v2)
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v4)))))
                (let v6
                       = MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v4) in
                 coe
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_936
                      (coe v6)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4))
                      (coe v2)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v4)))))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C__'8759'__236
                (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
                (MAlonzo.Code.Once.CCC.Codegen.SlotBudget.d_ir'45'slots'45'below'45'under'45'lab_1944
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v4))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v4))
                   (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))))
             (coe
                du_fns'45'slots_128 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v2)
                   (coe v4))
                (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImageFacts.image-slots
d_image'45'slots_152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Codegen.SlotSeg.T_AllSeg_224
d_image'45'slots_152 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.SlotSeg.C__'8759'__236
      (coe MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_sb'45'none_40)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotSeg.du_allseg'45''43''43'_244
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_link'45'top_2376
            (coe d_d_162 (coe v0) (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_854 v0
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) v2))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_ir'45'slots'45'below'45'top_1982
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (0 :: Integer))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe
            du_fns'45'slots_128
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_878
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (0 :: Integer))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
            (coe
               addInt (coe (1 :: Integer))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_946
                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
                  (coe v2)))
            (coe v1)))
-- Once.CCC.Codegen.ProgramImageFacts._.d
d_d_162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_d_162 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_top'45'done_30
      (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
         (coe v2))
-- Once.CCC.Codegen.ProgramImageFacts.fn-labels
d_fn'45'labels_170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fn'45'labels_170 ~v0 v1 v2 = du_fn'45'labels_170 v1 v2
du_fn'45'labels_170 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fn'45'labels_170 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Once.CCC.Codegen.LabelSeg.du_li'45'none_54)
      (MAlonzo.Code.Once.CCC.Codegen.LabelScope.d_linked'45'labels'45'lab_3540
         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))
         (coe v0))
-- Once.CCC.Codegen.ProgramImageFacts.fn-agree
d_fn'45'agree_180 ::
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
d_fn'45'agree_180 = erased
-- Once.CCC.Codegen.ProgramImageFacts.fns-labels
d_fns'45'labels_190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fns'45'labels_190 ~v0 v1 v2 = du_fns'45'labels_190 v1 v2
du_fns'45'labels_190 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fns'45'labels_190 v0 v1
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
                (coe du_fn'45'labels_170 (coe v0) (coe v2)))
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
                   du_fns'45'labels_190
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                      (coe v2))
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImageFacts.fns-agree
d_fns'45'agree_204 ::
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
d_fns'45'agree_204 = erased
-- Once.CCC.Codegen.ProgramImageFacts.image-agree
d_image'45'agree_218 ::
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
d_image'45'agree_218 = erased
-- Once.CCC.Codegen.ProgramImageFacts._.L
d_L_228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_L_228 v0 ~v1 v2 = du_L_228 v0 v2
du_L_228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_L_228 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_946
      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
      (coe v1)
-- Once.CCC.Codegen.ProgramImageFacts._.d
d_d_230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_d_230 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_top'45'done_30
      (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v1)
         (coe v2))
-- Once.CCC.Codegen.ProgramImageFacts._._.fetch
d_fetch_240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
d_fetch_240 ~v0 ~v1 = du_fetch_240
du_fetch_240 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
du_fetch_240 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.CCC.Codegen.ProgramImageFacts._._.find-label
d_find'45'label_242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_242 ~v0 v1 = du_find'45'label_242 v1
du_find'45'label_242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_242 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.CCC.Codegen.ProgramImageFacts._.fetch≡at
d_fetch'8801'at_250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'8801'at_250 = erased
-- Once.CCC.Codegen.ProgramImageFacts._.image-jump-in-segment
d_image'45'jump'45'in'45'segment_274 ::
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
d_image'45'jump'45'in'45'segment_274 = erased
