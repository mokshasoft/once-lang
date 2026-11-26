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

module MAlonzo.Code.Once.Measure where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses
import qualified MAlonzo.Code.Once.CCC.Codegen.RoomChecks
import qualified MAlonzo.Code.Once.CCC.Codegen.StackDepth
import qualified MAlonzo.Code.Once.CCC.Codegen.StackDepthTable
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CompileSrc
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.LinCore.ExprBuild
import qualified MAlonzo.Code.Once.LinCore.ExprImage
import qualified MAlonzo.Code.Once.Measure.Copies
import qualified MAlonzo.Code.Once.Measure.Image
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Measure.kind-name
d_kind'45'name_4 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_kind'45'name_4 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'call_62 v1
        -> coe ("call" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'clo_64
        -> coe ("closure-call" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'sig_66 v1
        -> coe ("sigop" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'entry_68 v1 v2
        -> coe ("entry" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'label_70 v1
        -> coe ("label" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'jump_72 v1
        -> coe ("jump" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'branch_74 v1
        -> coe ("branch" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'ret_76
        -> coe ("return" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'start_78 v1
        -> coe ("start" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'none_80
        -> coe ("other" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.first-fail
d_first'45'fail_6 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_256 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_first'45'fail_6 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe ("none" :: Data.Text.Text)
      (:) v4 v5
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_ok'45'at_424 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_126 (coe v1)
                   (coe v4))
                (coe v4))
             (coe
                d_first'45'fail_6 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_126 (coe v1)
                   (coe v4))
                (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v5))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_kind'45'name_4
                         (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_kind_82 (coe v4)))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (" cost=" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (coe
                               MAlonzo.Code.Data.Nat.Show.d_show_56
                               (MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_cost_354
                                  (coe v0)
                                  (coe
                                     MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_126 (coe v1)
                                     (coe v4))
                                  (coe v4)))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (" past=" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.Nat.Show.d_show_56
                                  (MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_pastO_292
                                     (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_126 (coe v1)
                                        (coe v4))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.counts
d_counts_24 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_256 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_counts_24 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("unbounded-entries=" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" checked-calls=" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (" calls=" :: Data.Text.Text)
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v5)))))
      (:) v6 v7
        -> coe
             d_go_56 (coe v0) (coe v1) (coe v6) (coe v7) (coe v3) (coe v4)
             (coe v5)
             (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_kind_82 (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure._.o′
d_o'8242'_54 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_256 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36
d_o'8242'_54 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 = du_o'8242'_54 v1 v2
du_o'8242'_54 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36
du_o'8242'_54 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_126 (coe v0)
      (coe v1)
-- Once.Measure._.go
d_go_56 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_256 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_go_56 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = d_counts_24
              (coe v0) (coe du_o'8242'_54 (coe v1) (coe v2)) (coe v3) (coe v4)
              (coe v5) (coe v6) in
    coe
      (case coe v7 of
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'call_62 v9
           -> coe
                d_counts_24 (coe v0) (coe du_o'8242'_54 (coe v1) (coe v2)) (coe v3)
                (coe v4)
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_chk_300 (coe v0)
                      (coe du_o'8242'_54 (coe v1) (coe v2)) (coe v9))
                   (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v5))
                (coe addInt (coe (1 :: Integer)) (coe v6))
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'clo_64
           -> coe
                d_counts_24 (coe v0) (coe du_o'8242'_54 (coe v1) (coe v2)) (coe v3)
                (coe v4)
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_clo'45'chk_282 v0
                      (coe du_o'8242'_54 (coe v1) (coe v2)))
                   (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v5))
                (coe addInt (coe (1 :: Integer)) (coe v6))
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'entry_68 v9 v10
           -> coe
                d_counts_24 (coe v0) (coe du_o'8242'_54 (coe v1) (coe v2)) (coe v3)
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                   (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_bnd_274 v0 v9)
                   (coe v4) (coe addInt (coe (1 :: Integer)) (coe v4)))
                (coe v5) (coe v6)
         _ -> coe v8)
-- Once.Measure.depth-diag
d_depth'45'diag_62 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_depth'45'diag_62 v0
  = coe
      d_go_70 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.StackDepthTable.d_table_846 (coe v0))
-- Once.Measure._.go
d_go_70 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_256 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_go_70 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("depth-table: " :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_consistent'63'_464
               (coe v1) (coe d_P_78 (coe v0) (coe v1)))
            (coe ("certified" :: Data.Text.Text))
            (coe ("FALLBACK" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (" past0=" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (coe
                  MAlonzo.Code.Data.Nat.Show.d_show_56
                  (MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_past'8320'_280
                     (coe v1)))
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (" " :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_counts_24
                        (coe v1)
                        (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
                        (coe v0) (coe (0 :: Integer)) (coe (0 :: Integer))
                        (coe (0 :: Integer)))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (" first-fail=" :: Data.Text.Text)
                        (d_first'45'fail_6
                           (coe v1)
                           (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
                           (coe (0 :: Integer)) (coe d_P_78 (coe v0) (coe v1)))))))))
-- Once.Measure._._.P
d_P_78 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_256 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_P_78 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.RoomChecks.d_checks_108 (coe v1)
      (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
      (coe v0)
-- Once.Measure.at
d_at_82 ::
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_at_82 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (MAlonzo.Code.Once.Measure.Image.d_show'45'stats_108
                          (coe
                             MAlonzo.Code.Once.Measure.Image.d_image'45'stats_106
                             (MAlonzo.Code.Once.CCC.Codegen.RoomChecks.d_room'45'checks_166
                                (coe d_im_96 (coe v0) (coe v3) (coe v4)))))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("\n" :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (d_depth'45'diag_62 (coe d_im_96 (coe v0) (coe v3) (coe v4)))
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("\n(built) " :: Data.Text.Text)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (d_depth'45'diag_62 (coe d_imc_98 (coe v0) (coe v3) (coe v4)))
                                   (coe
                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                      ("\n" :: Data.Text.Text)
                                      (coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                         ("copies: dups=" :: Data.Text.Text)
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            (coe
                                               MAlonzo.Code.Data.Nat.Show.d_show_56
                                               (MAlonzo.Code.Once.Measure.Copies.d_dups_666
                                                  (coe
                                                     MAlonzo.Code.Once.Measure.Copies.du_defs_768
                                                     (coe
                                                        MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1338
                                                        (coe
                                                           MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1346
                                                           (coe
                                                              MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                                                              (coe
                                                                 MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
                                                           (coe
                                                              MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1516
                                                              (coe v0)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                     (coe
                                                        MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1340
                                                        (coe
                                                           MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1346
                                                           (coe
                                                              MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                                                              (coe
                                                                 MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
                                                           (coe
                                                              MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1516
                                                              (coe v0)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               (" dup-cells=" :: Data.Text.Text)
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Show.d_show_56
                                                     (MAlonzo.Code.Once.Measure.Copies.d_dup'45'cells_668
                                                        (coe
                                                           MAlonzo.Code.Once.Measure.Copies.du_defs_768
                                                           (coe
                                                              MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1338
                                                              (coe
                                                                 MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1346
                                                                 (coe
                                                                    MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                                                                    (coe
                                                                       MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
                                                                 (coe
                                                                    MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1516
                                                                    (coe v0)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                           (coe
                                                              MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1340
                                                              (coe
                                                                 MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1346
                                                                 (coe
                                                                    MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                                                                    (coe
                                                                       MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
                                                                 (coe
                                                                    MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1516
                                                                    (coe v0)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                                                  (coe
                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                     (" bcopy-cells=" :: Data.Text.Text)
                                                     (coe
                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Show.d_show_56
                                                           (MAlonzo.Code.Once.Measure.Copies.d_bcopy'45'cells_670
                                                              (coe
                                                                 MAlonzo.Code.Once.Measure.Copies.du_defs_768
                                                                 (coe
                                                                    MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1338
                                                                    (coe
                                                                       MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1346
                                                                       (coe
                                                                          MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                                                                          (coe
                                                                             MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
                                                                       (coe
                                                                          MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1516
                                                                          (coe v0)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                                 (coe
                                                                    MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1340
                                                                    (coe
                                                                       MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1346
                                                                       (coe
                                                                          MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                                                                          (coe
                                                                             MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
                                                                       (coe
                                                                          MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1516
                                                                          (coe v0)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           (" clo-cells=" :: Data.Text.Text)
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Show.d_show_56
                                                              (MAlonzo.Code.Once.Measure.Copies.d_clo'45'cells_672
                                                                 (coe
                                                                    MAlonzo.Code.Once.Measure.Copies.du_defs_768
                                                                    (coe
                                                                       MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1338
                                                                       (coe
                                                                          MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1346
                                                                          (coe
                                                                             MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                                                                             (coe
                                                                                MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
                                                                          (coe
                                                                             MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1516
                                                                             (coe v0)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                                    (coe
                                                                       MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1340
                                                                       (coe
                                                                          MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1346
                                                                          (coe
                                                                             MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                                                                             (coe
                                                                                MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
                                                                          (coe
                                                                             MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1516
                                                                             (coe v0)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Once.Measure.Image.d_show'45'stats_108
                (coe
                   MAlonzo.Code.Once.Measure.Image.d_image'45'stats_106
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure._.im
d_im_96 ::
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_im_96 v0 v1 v2
  = coe
      MAlonzo.Code.Once.LinCore.ExprImage.d_imageAt_10
      (coe
         MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1516 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe v1) (coe v2)
-- Once.Measure._.imc
d_imc_98 ::
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_imc_98 v0 v1 v2
  = coe
      MAlonzo.Code.Once.LinCore.ExprImage.d_imageAt'8344'_48
      (MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
         (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.C_alloc'45'pool_382)
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1516 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      v1 v2
-- Once.Measure.stats-src
d_stats'45'src_100 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_stats'45'src_100 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             d_at_82 (coe v1)
             (coe MAlonzo.Code.Once.CompileSrc.d_mainOf_1810 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.statsOf
d_statsOf_106 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_statsOf_106 ~v0 v1 = du_statsOf_106 v1
du_statsOf_106 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_statsOf_106 v0
  = coe
      d_stats'45'src_100
      (coe
         MAlonzo.Code.Once.CompileSrc.d_srcModule_1760
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
