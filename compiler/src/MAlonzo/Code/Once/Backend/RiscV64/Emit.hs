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

module MAlonzo.Code.Once.Backend.RiscV64.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Backend.RiscV64.Syntax

-- Once.Backend.RiscV64.Emit.unlines
d_unlines_8 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_unlines_8 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_unlines_8 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe v1
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.RiscV64.Emit.showℤ
d_showℤ_16 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showℤ_16 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0
      _ -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("-" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.Nat.Show.d_show_56
                (subInt (coe (0 :: Integer)) (coe v0)))
-- Once.Backend.RiscV64.Emit.regToText
d_regToText_26 ::
  MAlonzo.Code.Once.Backend.RiscV64.Syntax.T_Reg_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_regToText_26 v0
  = case coe v0 of
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_zero_10
        -> coe ("zero" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ra_12
        -> coe ("ra" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sp_14
        -> coe ("sp" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_gp_16
        -> coe ("gp" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_tp_18
        -> coe ("tp" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t0_20
        -> coe ("t0" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t1_22
        -> coe ("t1" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t2_24
        -> coe ("t2" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s0_26
        -> coe ("s0" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s1_28
        -> coe ("s1" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a0_30
        -> coe ("a0" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a1_32
        -> coe ("a1" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a2_34
        -> coe ("a2" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a3_36
        -> coe ("a3" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a4_38
        -> coe ("a4" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a5_40
        -> coe ("a5" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a6_42
        -> coe ("a6" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_a7_44
        -> coe ("a7" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s2_46
        -> coe ("s2" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s3_48
        -> coe ("s3" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s4_50
        -> coe ("s4" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s5_52
        -> coe ("s5" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s6_54
        -> coe ("s6" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s7_56
        -> coe ("s7" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s8_58
        -> coe ("s8" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s9_60
        -> coe ("s9" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s10_62
        -> coe ("s10" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_s11_64
        -> coe ("s11" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t3_66
        -> coe ("t3" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t4_68
        -> coe ("t4" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t5_70
        -> coe ("t5" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_t6_72
        -> coe ("t6" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.RiscV64.Emit.instrToText
d_instrToText_28 ::
  MAlonzo.Code.Once.Backend.RiscV64.Syntax.T_Instr_86 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instrToText_28 v0
  = case coe v0 of
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_add_88 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    add " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_regToText_26 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sub_90 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sub " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_regToText_26 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_and_92 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    and " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_regToText_26 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_or_94 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    or " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_regToText_26 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_xor_96 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    xor " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_regToText_26 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sll_98 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sll " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_regToText_26 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_srl_100 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    srl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_regToText_26 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sra_102 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sra " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_regToText_26 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_slt_104 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    slt " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_regToText_26 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sltu_106 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sltu " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_regToText_26 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_addi_108 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addi " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_andi_110 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    andi " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ori_112 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    ori " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_xori_114 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    xori " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_slti_116 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    slti " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sltiu_118 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sltiu " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_slli_120 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    slli " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_srli_122 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    srli " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_srai_124 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    srai " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ld_126 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    ld " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_lw_128 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    lw " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_lwu_130 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    lwu " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_lh_132 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    lh " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_lhu_134 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    lhu " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_lb_136 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    lb " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_lbu_138 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    lbu " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sd_140 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sw_142 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sw " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sh_144 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sh " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_sb_146 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sb " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_beq_148 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    beq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", .L" :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_bne_150 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    bne " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", .L" :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_blt_152 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    blt " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", .L" :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_bge_154 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    bge " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", .L" :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_bltu_156 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    bltu " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", .L" :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_bgeu_158 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    bgeu " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_regToText_26 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", .L" :: Data.Text.Text) (d_showℤ_16 (coe v3))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_lui_160 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    lui " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showℤ_16 (coe v2))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_auipc_162 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    auipc " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showℤ_16 (coe v2))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_jal_164 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", .L" :: Data.Text.Text) (d_showℤ_16 (coe v2))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_jalr_166 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    jalr " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 (d_showℤ_16 (coe v3))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_regToText_26 (coe v2)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_li_168 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    li " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_showℤ_16 (coe v2))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_mv_170 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mv " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_regToText_26 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text) (d_regToText_26 (coe v2))))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_j_172 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    j .L" :: Data.Text.Text) (d_showℤ_16 (coe v1))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_call_174 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    call .L" :: Data.Text.Text) (d_showℤ_16 (coe v1))
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ret_176
        -> coe ("    ret" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_nop_178
        -> coe ("    nop" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_ebreak_180
        -> coe ("    ebreak" :: Data.Text.Text)
      MAlonzo.Code.Once.Backend.RiscV64.Syntax.C_label_182 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".L" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (":" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.RiscV64.Emit.programToText
d_programToText_278 ::
  [MAlonzo.Code.Once.Backend.RiscV64.Syntax.T_Instr_86] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_programToText_278 v0
  = coe
      d_unlines_8
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22 (coe d_instrToText_28)
         (coe v0))
