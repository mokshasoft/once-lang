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
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg

-- Once.CCC.Target.RiscV64.Emit.showLabel
d_showLabel_10 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showLabel_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Label.C_once_24 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("once_" :: Data.Text.Text)
             (MAlonzo.Code.Once.CCC.Label.d_showLabelId_248 (coe v1))
      MAlonzo.Code.Once.CCC.Label.C_sigop_26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("sigops_" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("_" :: Data.Text.Text)
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)))
      MAlonzo.Code.Once.CCC.Label.C_thunk_28 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("_thunk_" :: Data.Text.Text)
             (MAlonzo.Code.Once.CCC.Label.d_showLabelId_248 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Emit.showInstr
d_showInstr_20 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showInstr_20 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    ld " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
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
                            (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v2))
                            (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
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
                            (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v2))
                            (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    add " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52
                            (coe v3))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sub " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52
                            (coe v3))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addi " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v3))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    li " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_auipc_24 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    auipc " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla_26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    lla " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", .L_thunk_" :: Data.Text.Text)
                   (MAlonzo.Code.Once.CCC.Label.d_showLabelId_248 (coe v2))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mv " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v2))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    beq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", .L" :: Data.Text.Text) (d_showLabel_10 (coe v3))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bne_32 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    bne " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", .L" :: Data.Text.Text) (d_showLabel_10 (coe v3))))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jal_34 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", .L" :: Data.Text.Text) (d_showLabel_10 (coe v2))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_36 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jalr " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_38 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    j .L" :: Data.Text.Text) (d_showLabel_10 (coe v1))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ret_40
        -> coe ("    ret" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call_42 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    call " :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_44 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    call " :: Data.Text.Text) v1
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_nop_46
        -> coe ("    nop" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_48
        -> coe ("    unimp" :: Data.Text.Text)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showLabel_10 (coe v1)) (":" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Emit.instrToLine
d_instrToLine_98 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToLine_98 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_showInstr_20 (coe v0)) ("\n" :: Data.Text.Text)
-- Once.CCC.Target.RiscV64.Emit.programToText
d_programToText_102 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_programToText_102
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (d_instrToLine_98 (coe v0))))
      (coe ("" :: Data.Text.Text))
