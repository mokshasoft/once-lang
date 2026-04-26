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

module MAlonzo.Code.Once.CCC.Target.RiscV64.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax

-- Once.CCC.Target.RiscV64.Emit.showReg
d_showReg_10 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Reg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showReg_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_zero_12
        -> coe ("zero" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ra_14
        -> coe ("ra" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sp_16
        -> coe ("sp" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_fp_18
        -> coe ("fp" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20
        -> coe ("a0" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a1_22
        -> coe ("a1" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a2_24
        -> coe ("a2" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a3_26
        -> coe ("a3" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a4_28
        -> coe ("a4" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a5_30
        -> coe ("a5" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a6_32
        -> coe ("a6" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a7_34
        -> coe ("a7" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s1_36
        -> coe ("s1" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s2_38
        -> coe ("s2" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s3_40
        -> coe ("s3" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_s4_42
        -> coe ("s4" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t0_44
        -> coe ("t0" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t1_46
        -> coe ("t1" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t2_48
        -> coe ("t2" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t3_50
        -> coe ("t3" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_t4_52
        -> coe ("t4" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Emit.showInstr
d_showInstr_12 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_54 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showInstr_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_56 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    ld " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_showReg_10 (coe v2)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_58 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_showReg_10 (coe v2)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_60 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    add " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showReg_10 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_showReg_10 (coe v3))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_62 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sub " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showReg_10 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_showReg_10 (coe v3))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_64 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addi " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showReg_10 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v3))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_66 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    li " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_auipc_68 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    auipc " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_70 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mv " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showReg_10 (coe v2))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_72 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    beq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showReg_10 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", .L" :: Data.Text.Text)
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bne_74 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    bne " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showReg_10 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", .L" :: Data.Text.Text)
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jal_76 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", .L" :: Data.Text.Text)
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_78 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jalr " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showReg_10 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showReg_10 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_80 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    j .L" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ret_82
        -> coe ("    ret" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call_84 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    call " :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_nop_86
        -> coe ("    nop" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_88
        -> coe ("    unimp" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_90 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (":" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Emit.instrToLine
d_instrToLine_84 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_54 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToLine_84 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_showInstr_12 (coe v0)) ("\n" :: Data.Text.Text)
-- Once.CCC.Target.RiscV64.Emit.programToText
d_programToText_88 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_54] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_programToText_88
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (d_instrToLine_84 (coe v0))))
      (coe ("" :: Data.Text.Text))
