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

module MAlonzo.Code.Once.Measure.Image where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.Measure.Image.ImageStats
d_ImageStats_6 = ()
data T_ImageStats_6
  = C_mk'45'stats_32 Integer Integer Integer Integer Integer Integer
-- Once.Measure.Image.ImageStats.instrs
d_instrs_20 :: T_ImageStats_6 -> Integer
d_instrs_20 v0
  = case coe v0 of
      C_mk'45'stats_32 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Image.ImageStats.heap-sites
d_heap'45'sites_22 :: T_ImageStats_6 -> Integer
d_heap'45'sites_22 v0
  = case coe v0 of
      C_mk'45'stats_32 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Image.ImageStats.heap-cells
d_heap'45'cells_24 :: T_ImageStats_6 -> Integer
d_heap'45'cells_24 v0
  = case coe v0 of
      C_mk'45'stats_32 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Image.ImageStats.frames
d_frames_26 :: T_ImageStats_6 -> Integer
d_frames_26 v0
  = case coe v0 of
      C_mk'45'stats_32 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Image.ImageStats.frame-max
d_frame'45'max_28 :: T_ImageStats_6 -> Integer
d_frame'45'max_28 v0
  = case coe v0 of
      C_mk'45'stats_32 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Image.ImageStats.frame-sum
d_frame'45'sum_30 :: T_ImageStats_6 -> Integer
d_frame'45'sum_30 v0
  = case coe v0 of
      C_mk'45'stats_32 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Image.empty
d_empty_34 :: T_ImageStats_6
d_empty_34
  = coe
      C_mk'45'stats_32 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer))
-- Once.Measure.Image.frame
d_frame_36 :: Integer -> T_ImageStats_6 -> T_ImageStats_6
d_frame_36 v0 v1
  = case coe v1 of
      C_mk'45'stats_32 v2 v3 v4 v5 v6 v7
        -> coe
             C_mk'45'stats_32 (coe v2) (coe v3) (coe v4)
             (coe addInt (coe (1 :: Integer)) (coe v5))
             (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v0) (coe v6))
             (coe addInt (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Image.step
d_step_52 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  T_ImageStats_6 -> T_ImageStats_6
d_step_52 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2314 v2
        -> case coe v1 of
             C_mk'45'stats_32 v3 v4 v5 v6 v7 v8
               -> coe
                    C_mk'45'stats_32 (coe v3)
                    (coe addInt (coe (1 :: Integer)) (coe v4))
                    (coe addInt (coe v2) (coe v5)) (coe v6) (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320 v2
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v3 v4
               -> coe d_frame_36 (coe v4) (coe v1)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v3
               -> coe d_frame_36 (coe v3) (coe v1)
             _ -> coe v1
      _ -> coe v1
-- Once.Measure.Image.count
d_count_78 ::
  T_ImageStats_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  T_ImageStats_6
d_count_78 v0 v1
  = case coe v0 of
      C_mk'45'stats_32 v2 v3 v4 v5 v6 v7
        -> coe
             d_step_52 (coe v1)
             (coe
                C_mk'45'stats_32 (coe addInt (coe (1 :: Integer)) (coe v2))
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Image.go
d_go_94 ::
  T_ImageStats_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_ImageStats_6
d_go_94 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe d_go_94 (coe d_count_78 (coe v0) (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Image.image-stats
d_image'45'stats_104 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  T_ImageStats_6
d_image'45'stats_104 = coe d_go_94 (coe d_empty_34)
-- Once.Measure.Image.show-stats
d_show'45'stats_106 ::
  T_ImageStats_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'stats_106 v0
  = case coe v0 of
      C_mk'45'stats_32 v1 v2 v3 v4 v5 v6
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("instrs " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\nheap-sites " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("\nheap-cells " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("\nframes " :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("\nframe-max " :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v5)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("\nframe-sum " :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v6)
                                              ("\n" :: Data.Text.Text))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
