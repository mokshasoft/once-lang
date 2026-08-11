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

module MAlonzo.Code.Once.CCC.Codegen.EmittedWF where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Codegen.EmittedWF.labels-def
d_labels'45'def_8 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_22]
d_labels'45'def_8 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_labels'45'def'45'i_10 (coe v1))
             (coe d_labels'45'def_8 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.EmittedWF.labels-def-i
d_labels'45'def'45'i_10 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_22]
d_labels'45'def'45'i_10 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2348 v2 v3
           -> coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_labels'45'def_8 (coe v2)) (coe d_labels'45'def_8 (coe v3))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2352 v2
           -> coe d_labels'45'def_8 (coe v2)
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2274 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_24 (coe v3))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2282 v3 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.CCC.Label.C_thunk_28 (coe v3))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.EmittedWF.labels-ref
d_labels'45'ref_26 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_22]
d_labels'45'ref_26 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_labels'45'ref'45'i_28 (coe v1))
             (coe d_labels'45'ref_26 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.EmittedWF.labels-ref-i
d_labels'45'ref'45'i_28 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_22]
d_labels'45'ref'45'i_28 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2342 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Label.C_thunk_28 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2348 v2 v3
           -> coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_labels'45'ref_26 (coe v2)) (coe d_labels'45'ref_26 (coe v3))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2352 v2
           -> coe d_labels'45'ref_26 (coe v2)
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2276 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_24 (coe v3))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2278 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_24 (coe v3))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2280 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_24 (coe v3))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.EmittedWF.EmittedWF
d_EmittedWF_50 a0 = ()
data T_EmittedWF_50
  = C_mkEmittedWF_66 MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
                     MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.CCC.Codegen.EmittedWF.EmittedWF.labels-unique
d_labels'45'unique_60 ::
  T_EmittedWF_50 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_labels'45'unique_60 v0
  = case coe v0 of
      C_mkEmittedWF_66 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.EmittedWF.EmittedWF.labels-resolvable
d_labels'45'resolvable_64 ::
  T_EmittedWF_50 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_labels'45'resolvable_64 v0
  = case coe v0 of
      C_mkEmittedWF_66 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
