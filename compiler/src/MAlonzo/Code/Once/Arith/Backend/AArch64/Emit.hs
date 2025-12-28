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

module MAlonzo.Code.Once.Arith.Backend.AArch64.Emit where

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
import qualified MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax

-- Once.Arith.Backend.AArch64.Emit.unlines
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
-- Once.Arith.Backend.AArch64.Emit.gprToText
d_gprToText_18 ::
  MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_GPReg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_gprToText_18 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x0_12
        -> coe ("x0" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x1_14
        -> coe ("x1" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x2_16
        -> coe ("x2" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x3_18
        -> coe ("x3" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x4_20
        -> coe ("x4" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x5_22
        -> coe ("x5" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x6_24
        -> coe ("x6" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x7_26
        -> coe ("x7" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x8_28
        -> coe ("x8" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x9_30
        -> coe ("x9" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x10_32
        -> coe ("x10" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x11_34
        -> coe ("x11" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x12_36
        -> coe ("x12" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x13_38
        -> coe ("x13" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x14_40
        -> coe ("x14" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x15_42
        -> coe ("x15" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x16_44
        -> coe ("x16" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x17_46
        -> coe ("x17" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x18_48
        -> coe ("x18" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x19_50
        -> coe ("x19" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x20_52
        -> coe ("x20" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x21_54
        -> coe ("x21" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x22_56
        -> coe ("x22" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x23_58
        -> coe ("x23" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x24_60
        -> coe ("x24" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x25_62
        -> coe ("x25" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x26_64
        -> coe ("x26" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x27_66
        -> coe ("x27" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x28_68
        -> coe ("x28" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x29_70
        -> coe ("x29" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_x30_72
        -> coe ("x30" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.AArch64.Emit.fpToText
d_fpToText_20 ::
  MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_FPReg_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fpToText_20 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d0_76
        -> coe ("d0" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d1_78
        -> coe ("d1" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d2_80
        -> coe ("d2" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d3_82
        -> coe ("d3" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d4_84
        -> coe ("d4" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d5_86
        -> coe ("d5" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d6_88
        -> coe ("d6" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d7_90
        -> coe ("d7" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d8_92
        -> coe ("d8" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d9_94
        -> coe ("d9" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d10_96
        -> coe ("d10" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d11_98
        -> coe ("d11" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d12_100
        -> coe ("d12" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d13_102
        -> coe ("d13" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d14_104
        -> coe ("d14" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d15_106
        -> coe ("d15" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d16_108
        -> coe ("d16" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d17_110
        -> coe ("d17" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d18_112
        -> coe ("d18" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d19_114
        -> coe ("d19" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d20_116
        -> coe ("d20" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d21_118
        -> coe ("d21" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d22_120
        -> coe ("d22" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d23_122
        -> coe ("d23" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d24_124
        -> coe ("d24" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d25_126
        -> coe ("d25" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d26_128
        -> coe ("d26" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d27_130
        -> coe ("d27" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d28_132
        -> coe ("d28" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d29_134
        -> coe ("d29" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d30_136
        -> coe ("d30" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d31_138
        -> coe ("d31" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.AArch64.Emit.fpToTextS
d_fpToTextS_22 ::
  MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_FPReg_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fpToTextS_22 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d0_76
        -> coe ("s0" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d1_78
        -> coe ("s1" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d2_80
        -> coe ("s2" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d3_82
        -> coe ("s3" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d4_84
        -> coe ("s4" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d5_86
        -> coe ("s5" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d6_88
        -> coe ("s6" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d7_90
        -> coe ("s7" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d8_92
        -> coe ("s8" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d9_94
        -> coe ("s9" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d10_96
        -> coe ("s10" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d11_98
        -> coe ("s11" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d12_100
        -> coe ("s12" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d13_102
        -> coe ("s13" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d14_104
        -> coe ("s14" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d15_106
        -> coe ("s15" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d16_108
        -> coe ("s16" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d17_110
        -> coe ("s17" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d18_112
        -> coe ("s18" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d19_114
        -> coe ("s19" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d20_116
        -> coe ("s20" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d21_118
        -> coe ("s21" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d22_120
        -> coe ("s22" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d23_122
        -> coe ("s23" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d24_124
        -> coe ("s24" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d25_126
        -> coe ("s25" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d26_128
        -> coe ("s26" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d27_130
        -> coe ("s27" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d28_132
        -> coe ("s28" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d29_134
        -> coe ("s29" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d30_136
        -> coe ("s30" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_d31_138
        -> coe ("s31" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.AArch64.Emit.opToText
d_opToText_24 ::
  MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_Operand_146 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_opToText_24 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_regOp_148 v1
        -> coe d_gprToText_18 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_immOp_150 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("#" :: Data.Text.Text)
             (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.AArch64.Emit.fpOpToText
d_fpOpToText_30 ::
  MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_FPOperand_152 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fpOpToText_30 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fpRegOp_154 v1
        -> coe d_fpToText_20 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.AArch64.Emit.condToText
d_condToText_34 ::
  MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_Cond_156 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_condToText_34 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_cond'45'eq_158
        -> coe ("eq" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_cond'45'ne_160
        -> coe ("ne" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_cond'45'lt_162
        -> coe ("lt" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_cond'45'le_164
        -> coe ("le" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_cond'45'gt_166
        -> coe ("gt" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_cond'45'ge_168
        -> coe ("ge" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.AArch64.Emit.intInstrToText
d_intInstrToText_36 ::
  MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_IntInstr_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_intInstrToText_36 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_mov_172 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mov " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_opToText_24 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_movz_174 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movz " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", #" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", lsl #" :: Data.Text.Text)
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_movk_176 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movk " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", #" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", lsl #" :: Data.Text.Text)
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_add_178 v1 v2 v3
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
                         (", " :: Data.Text.Text) (d_opToText_24 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_sub_180 v1 v2 v3
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
                         (", " :: Data.Text.Text) (d_opToText_24 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_mul_182 v1 v2 v3
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
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_sdiv_184 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sdiv " :: Data.Text.Text)
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
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_msub_186 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    msub " :: Data.Text.Text)
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
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_gprToText_18 (coe v3))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (", " :: Data.Text.Text) (d_gprToText_18 (coe v4))))))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_neg_188 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    neg " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_gprToText_18 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_strPre_190 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    str " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", [sp, #-" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                      ("]!" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_ldrPost_192 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    ldr " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", [sp], #" :: Data.Text.Text)
                   (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_cmp_194 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmp " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_opToText_24 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_cset_196 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cset " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_gprToText_18 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_condToText_34 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.AArch64.Emit.fpInstrToText
d_fpInstrToText_106 ::
  MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_FPInstr_198 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fpInstrToText_106 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fmov_200 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmov " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_fpOpToText_30 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fadd_202 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fadd " :: Data.Text.Text)
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
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fsub_204 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fsub " :: Data.Text.Text)
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
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fmul_206 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmul " :: Data.Text.Text)
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
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fdiv_208 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fdiv " :: Data.Text.Text)
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
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fneg_210 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fneg " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToText_20 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_fpToText_20 (coe v2))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_faddS_212 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fadd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToTextS_22 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToTextS_22 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToTextS_22 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fsubS_214 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fsub " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToTextS_22 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToTextS_22 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToTextS_22 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fmulS_216 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmul " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToTextS_22 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToTextS_22 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToTextS_22 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fdivS_218 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fdiv " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToTextS_22 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_fpToTextS_22 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_fpToTextS_22 (coe v3))))))
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fnegS_220 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fneg " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_fpToTextS_22 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_fpToTextS_22 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.AArch64.Emit.instrToText
d_instrToText_168 ::
  MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_ArithInstr_222 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToText_168 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_intI_224 v1
        -> coe d_intInstrToText_36 (coe v1)
      MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.C_fpI_226 v1
        -> coe d_fpInstrToText_106 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.AArch64.Emit.emitProgram
d_emitProgram_174 ::
  [MAlonzo.Code.Once.Arith.Backend.AArch64.Syntax.T_ArithInstr_222] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emitProgram_174 v0
  = coe
      d_unlines_10
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22 (coe d_instrToText_168)
         (coe v0))
