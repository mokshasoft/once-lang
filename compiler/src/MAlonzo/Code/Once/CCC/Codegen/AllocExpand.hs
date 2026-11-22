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

module MAlonzo.Code.Once.CCC.Codegen.AllocExpand where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.CCC.Codegen.AllocExpand.Classes
d_Classes_8 = ()
data T_Classes_8
  = C_constructor_22 Integer (Integer -> Integer)
                     (Integer -> Integer)
-- Once.CCC.Codegen.AllocExpand.Classes.count
d_count_16 :: T_Classes_8 -> Integer
d_count_16 v0
  = case coe v0 of
      C_constructor_22 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpand.Classes.cls
d_cls_18 :: T_Classes_8 -> Integer -> Integer
d_cls_18 v0
  = case coe v0 of
      C_constructor_22 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpand.Classes.bsz
d_bsz_20 :: T_Classes_8 -> Integer -> Integer
d_bsz_20 v0
  = case coe v0 of
      C_constructor_22 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpand.w-s1
d_w'45's1_24 :: Integer
d_w'45's1_24 = coe (1 :: Integer)
-- Once.CCC.Codegen.AllocExpand.w-s2
d_w'45's2_26 :: Integer
d_w'45's2_26 = coe (2 :: Integer)
-- Once.CCC.Codegen.AllocExpand.head-word
d_head'45'word_28 :: Integer -> Integer
d_head'45'word_28 v0 = coe addInt (coe (3 :: Integer)) (coe v0)
-- Once.CCC.Codegen.AllocExpand.rec-words
d_rec'45'words_32 :: T_Classes_8 -> Integer
d_rec'45'words_32 v0
  = coe addInt (coe (3 :: Integer)) (coe d_count_16 (coe v0))
-- Once.CCC.Codegen.AllocExpand.alloc-owner
d_alloc'45'owner_36 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_alloc'45'owner_36
  = coe
      MAlonzo.Code.Once.Spec.Name.C_canonical_12
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe ("once-alloc" :: Data.Text.Text))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CCC.Codegen.AllocExpand.alloc-label
d_alloc'45'label_38 ::
  Integer -> Integer -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_alloc'45'label_38 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Label.C_mkLabelId_20
      (coe d_alloc'45'owner_36)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe addInt (coe addInt (coe v0) (coe v0)) (coe v1))
-- Once.CCC.Codegen.AllocExpand.lb-bump
d_lb'45'bump_44 ::
  Integer -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_lb'45'bump_44 v0
  = coe d_alloc'45'label_38 (coe v0) (coe (0 :: Integer))
-- Once.CCC.Codegen.AllocExpand.lb-done
d_lb'45'done_46 ::
  Integer -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_lb'45'done_46 v0
  = coe d_alloc'45'label_38 (coe v0) (coe (1 :: Integer))
-- Once.CCC.Codegen.AllocExpand.ImgL
d_ImgL_52 :: MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> ()
d_ImgL_52 = erased
-- Once.CCC.Codegen.AllocExpand.SiteL
d_SiteL_56 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> ()
d_SiteL_56 = erased
-- Once.CCC.Codegen.AllocExpand._.alloc-code
d_alloc'45'code_70 ::
  T_Classes_8 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_alloc'45'code_70 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2406)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2482
            (coe d_w'45's1_24))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2480
               (coe du_h_80 (coe v0) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2408)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2468
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2384
                        (coe d_lb'45'bump_44 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2474
                        (coe (0 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2482
                           (coe du_h_80 (coe v0) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2406)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2482
                                 (coe d_w'45's2_26))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2480
                                    (coe d_w'45's1_24))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2408)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2480
                                          (coe d_w'45's2_26))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2468
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2382
                                                (coe d_lb'45'done_46 (coe v1))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2468
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380
                                                   (coe d_lb'45'bump_44 (coe v1))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2480
                                                   (coe d_w'45's1_24))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2408)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2464
                                                         (coe d_bsz_20 v0 v2))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2468
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380
                                                               (coe d_lb'45'done_46 (coe v1))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))
-- Once.CCC.Codegen.AllocExpand._._.h
d_h_80 :: T_Classes_8 -> Integer -> Integer -> Integer
d_h_80 v0 ~v1 v2 = du_h_80 v0 v2
du_h_80 :: T_Classes_8 -> Integer -> Integer
du_h_80 v0 v1 = coe d_head'45'word_28 (coe d_cls_18 v0 v1)
-- Once.CCC.Codegen.AllocExpand._.free-code
d_free'45'code_82 ::
  T_Classes_8 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_free'45'code_82 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2482
         (coe d_w'45's1_24))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2480
            (coe d_h_90 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2476
               (coe (0 :: Integer)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2406)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2482
                     (coe d_h_90 (coe v0) (coe v1)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2480
                        (coe d_w'45's1_24))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Once.CCC.Codegen.AllocExpand._._.h
d_h_90 :: T_Classes_8 -> Integer -> Integer
d_h_90 v0 v1 = coe d_head'45'word_28 (coe d_cls_18 v0 v1)
-- Once.CCC.Codegen.AllocExpand._.heads
d_heads_92 ::
  T_Classes_8 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_heads_92 ~v0 v1 = du_heads_92 v1
du_heads_92 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
du_heads_92 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2482
                   (coe d_head'45'word_28 (coe v1)))
                (coe du_heads_92 (coe v1)))
-- Once.CCC.Codegen.AllocExpand._.setup
d_setup_96 ::
  T_Classes_8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_setup_96 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2482
         (coe d_w'45's1_24))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2406)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2482
               (coe d_w'45's2_26))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2464
                  (coe (1 :: Integer)))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe du_heads_92 (coe d_count_16 (coe v0)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2408)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2462
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2476
                              (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2480
                                 (coe d_w'45's2_26))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2408)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2480
                                       (coe d_w'45's1_24))
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
-- Once.CCC.Codegen.AllocExpand._.expand-at
d_expand'45'at_98 ::
  T_Classes_8 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_expand'45'at_98 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2464 v4
           -> coe d_alloc'45'code_70 (coe v0) (coe v1) (coe v4)
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2468 v4
           -> case coe v4 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe d_setup_96 (coe v0))
                _ -> coe v3
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'free'45'heap_2470 v4
           -> coe d_free'45'code_82 (coe v0) (coe v4)
         _ -> coe v3)
-- Once.CCC.Codegen.AllocExpand._.expand-from
d_expand'45'from_116 ::
  T_Classes_8 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_expand'45'from_116 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_expand'45'at_98 (coe v0) (coe v1) (coe v3))
             (coe
                d_expand'45'from_116 (coe v0)
                (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpand._.expand
d_expand_126 ::
  T_Classes_8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_expand_126 v0
  = coe d_expand'45'from_116 (coe v0) (coe (0 :: Integer))
