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

module MAlonzo.Code.Once.Arith.Backend.RiscV.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax

-- Once.Arith.Backend.RiscV.Emit.unlines
d_unlines_10 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_unlines_10 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_unlines_10 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe v1
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV.Emit.gprToText
d_gprToText_18 ::
  MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.T_GPReg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_gprToText_18 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x0_12
        -> coe ("x0" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x1_14
        -> coe ("x1" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x2_16
        -> coe ("x2" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x3_18
        -> coe ("x3" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x4_20
        -> coe ("x4" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x5_22
        -> coe ("x5" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x6_24
        -> coe ("x6" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x7_26
        -> coe ("x7" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x8_28
        -> coe ("x8" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x9_30
        -> coe ("x9" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x10_32
        -> coe ("x10" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x11_34
        -> coe ("x11" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x12_36
        -> coe ("x12" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x13_38
        -> coe ("x13" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x14_40
        -> coe ("x14" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x15_42
        -> coe ("x15" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x16_44
        -> coe ("x16" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x17_46
        -> coe ("x17" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x18_48
        -> coe ("x18" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x19_50
        -> coe ("x19" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x20_52
        -> coe ("x20" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x21_54
        -> coe ("x21" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x22_56
        -> coe ("x22" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x23_58
        -> coe ("x23" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x24_60
        -> coe ("x24" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x25_62
        -> coe ("x25" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x26_64
        -> coe ("x26" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x27_66
        -> coe ("x27" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x28_68
        -> coe ("x28" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x29_70
        -> coe ("x29" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x30_72
        -> coe ("x30" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_x31_74
        -> coe ("x31" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV.Emit.fpToText
d_fpToText_20 ::
  MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.T_FPReg_76 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fpToText_20 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f0_78
        -> coe ("f0" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f1_80
        -> coe ("f1" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f2_82
        -> coe ("f2" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f3_84
        -> coe ("f3" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f4_86
        -> coe ("f4" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f5_88
        -> coe ("f5" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f6_90
        -> coe ("f6" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f7_92
        -> coe ("f7" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f8_94
        -> coe ("f8" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f9_96
        -> coe ("f9" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f10_98
        -> coe ("f10" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f11_100
        -> coe ("f11" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f12_102
        -> coe ("f12" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f13_104
        -> coe ("f13" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f14_106
        -> coe ("f14" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f15_108
        -> coe ("f15" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f16_110
        -> coe ("f16" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f17_112
        -> coe ("f17" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f18_114
        -> coe ("f18" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f19_116
        -> coe ("f19" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f20_118
        -> coe ("f20" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f21_120
        -> coe ("f21" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f22_122
        -> coe ("f22" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f23_124
        -> coe ("f23" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f24_126
        -> coe ("f24" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f25_128
        -> coe ("f25" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f26_130
        -> coe ("f26" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f27_132
        -> coe ("f27" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f28_134
        -> coe ("f28" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f29_136
        -> coe ("f29" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f30_138
        -> coe ("f30" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_f31_140
        -> coe ("f31" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV.Emit.intInstrToText
d_intInstrToText_22 ::
  MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.T_IntInstr_158 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_intInstrToText_22 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_li_160 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    li " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_mv_162 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mv " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_add_164 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    add " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_gprToText_18 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_addi_166 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addi " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_sub_168 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sub " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_gprToText_18 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_mul_170 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mul " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_gprToText_18 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_div_172 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    div " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_gprToText_18 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_rem_174 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    rem " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_gprToText_18 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_neg_176 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    neg " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_sd_178 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                      ("(sp)" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_ld_180 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    ld " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                      ("(sp)" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_slt_182 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    slt " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_gprToText_18 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_sltu_184 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sltu " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_gprToText_18 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_slti_186 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    slti " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_sltiu_188 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sltiu " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_xori_190 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    xori " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_gprToText_18 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_seqz_192 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    seqz " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_snez_194 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    snez " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV.Emit.fpInstrToText
d_fpInstrToText_118 ::
  MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.T_FPInstr_196 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fpInstrToText_118 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_fmvD_198 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmv.d " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_fpToText_20 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_faddD_200 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fadd.d " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToText_20 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToText_20 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_fsubD_202 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fsub.d " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToText_20 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToText_20 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_fmulD_204 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmul.d " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToText_20 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToText_20 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_fdivD_206 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fdiv.d " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToText_20 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToText_20 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_fnegD_208 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fneg.d " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_fpToText_20 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_faddS_210 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fadd.s " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToText_20 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToText_20 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_fsubS_212 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fsub.s " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToText_20 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToText_20 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_fmulS_214 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmul.s " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToText_20 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToText_20 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_fdivS_216 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fdiv.s " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToText_20 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToText_20 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_fnegS_218 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fneg.s " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_fpToText_20 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV.Emit.instrToText
d_instrToText_180 ::
  MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.T_ArithInstr_220 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToText_180 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_intI_222 v1
        -> coe d_intInstrToText_22 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.C_fpI_224 v1
        -> coe d_fpInstrToText_118 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV.Emit.emitProgram
d_emitProgram_186 ::
  [MAlonzo.Code.Once.Arith.Backend.RiscV.Syntax.T_ArithInstr_220] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emitProgram_186 v0
  = coe
      d_unlines_10
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22 (coe d_instrToText_180)
         (coe v0))
