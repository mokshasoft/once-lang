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

module MAlonzo.Code.Once.CCC.Codegen.ProgramImage where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IRTy

-- Once.CCC.Codegen.ProgramImage.fn-image
d_fn'45'image_8 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_fn'45'image_8 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236
            (coe
               MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26
               (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1)))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_908
               (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1))
               (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
               (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
               (coe v0)
               (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1)))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_936
         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
         (coe v0)
         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1)))
-- Once.CCC.Codegen.ProgramImage.fn-next
d_fn'45'next_14 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 -> Integer
d_fn'45'next_14 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_946
      (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
      (coe v0)
      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))
-- Once.CCC.Codegen.ProgramImage.fns-image
d_fns'45'image_20 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_fns'45'image_20 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_fn'45'image_8 (coe v0) (coe v2))
             (coe
                d_fns'45'image_20 (coe d_fn'45'next_14 (coe v0) (coe v2)) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ProgramImage.top-done
d_top'45'done_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_top'45'done_30 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Label.C_mkLabelId_20 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_946
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1)))
-- Once.CCC.Codegen.ProgramImage.image-body
d_image'45'body_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_image'45'body_36 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_link'45'top_2376
         (coe d_top'45'done_30 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_854 v0
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))))
      (coe
         d_fns'45'image_20
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_946
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))))
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v1)))
-- Once.CCC.Codegen.ProgramImage.program-image
d_program'45'image_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_program'45'image_42 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_878
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1)))))
      (coe d_image'45'body_36 (coe v0) (coe v1))
