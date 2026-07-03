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

module MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.Machine.Compile
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.Arith.Backend.X86-64.Emit.arith-reg
d_arith'45'reg_10 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_arith'45'reg_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r8_26
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r9_28
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR2_16
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r10_30
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR3_18
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r11_32
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit.arith-disjoint
d_arith'45'disjoint_14 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'disjoint_14 = erased
-- Once.Arith.Backend.X86-64.Emit.reg-text
d_reg'45'text_16 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_reg'45'text_16 v0
  = coe
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.d_showReg_42
      (coe d_arith'45'reg_10 (coe v0))
-- Once.Arith.Backend.X86-64.Emit.scratch-text
d_scratch'45'text_20 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_20 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_scratch'45'text_20 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_mk'45'scratch_26 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("-" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe
                   MAlonzo.Code.Data.Nat.Show.d_show_56
                   (mulInt
                      (coe (8 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v1))))
                ("(%rsp)" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit.instr-text
d_instr'45'text_24 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_28 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instr'45'text_24 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_30 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq $" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_32 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_34 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_scratch'45'text_20 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_36 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_scratch'45'text_20 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_38 v1 v2
        -> coe du_path'45'load'45'text_66 (coe v1) (coe v2)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_42 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_44 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    imulq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_46 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    negq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_48 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %rax\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    testq " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v3))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", " :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (d_reg'45'text_16 (coe v3))
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("\n" :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("    jne 1f\n" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        ("    movq $-1, %rax\n" :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("    jmp 3f\n" :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("1:\n" :: Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 ("    cmpq $-1, " :: Data.Text.Text)
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    (d_reg'45'text_16 (coe v3))
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       ("\n" :: Data.Text.Text)
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          ("    jne 2f\n" :: Data.Text.Text)
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             ("    movabsq $0x8000000000000000, %rdx\n"
                                                              ::
                                                              Data.Text.Text)
                                                             (coe
                                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                ("    cmpq %rdx, %rax\n"
                                                                 ::
                                                                 Data.Text.Text)
                                                                (coe
                                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                   ("    jne 2f\n"
                                                                    ::
                                                                    Data.Text.Text)
                                                                   (coe
                                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                      ("    movq %rdx, %rax\n"
                                                                       ::
                                                                       Data.Text.Text)
                                                                      (coe
                                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                         ("    jmp 3f\n"
                                                                          ::
                                                                          Data.Text.Text)
                                                                         (coe
                                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                            ("2:\n"
                                                                             ::
                                                                             Data.Text.Text)
                                                                            (coe
                                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                               ("    cqto\n"
                                                                                ::
                                                                                Data.Text.Text)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                  ("    idivq "
                                                                                   ::
                                                                                   Data.Text.Text)
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                     (d_reg'45'text_16
                                                                                        (coe v3))
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                        ("\n"
                                                                                         ::
                                                                                         Data.Text.Text)
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                           ("3:\n"
                                                                                            ::
                                                                                            Data.Text.Text)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                              ("    movq %rax, "
                                                                                               ::
                                                                                               Data.Text.Text)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                                 (d_reg'45'text_16
                                                                                                    (coe
                                                                                                       v1))
                                                                                                 ("\n"
                                                                                                  ::
                                                                                                  Data.Text.Text)))))))))))))))))))))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_50 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %rax\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    testq " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v3))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", " :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (d_reg'45'text_16 (coe v3))
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("\n" :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("    jne 1f\n" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        ("    jmp 3f\n" :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("1:\n" :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("    cmpq $-1, " :: Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 (d_reg'45'text_16 (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("\n" :: Data.Text.Text)
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       ("    jne 2f\n" :: Data.Text.Text)
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          ("    movabsq $0x8000000000000000, %rdx\n"
                                                           ::
                                                           Data.Text.Text)
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             ("    cmpq %rdx, %rax\n"
                                                              ::
                                                              Data.Text.Text)
                                                             (coe
                                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                ("    jne 2f\n" :: Data.Text.Text)
                                                                (coe
                                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                   ("    xorl %eax, %eax\n"
                                                                    ::
                                                                    Data.Text.Text)
                                                                   (coe
                                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                      ("    jmp 3f\n"
                                                                       ::
                                                                       Data.Text.Text)
                                                                      (coe
                                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                         ("2:\n" :: Data.Text.Text)
                                                                         (coe
                                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                            ("    cqto\n"
                                                                             ::
                                                                             Data.Text.Text)
                                                                            (coe
                                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                               ("    idivq "
                                                                                ::
                                                                                Data.Text.Text)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                  (d_reg'45'text_16
                                                                                     (coe v3))
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                     ("\n"
                                                                                      ::
                                                                                      Data.Text.Text)
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                        ("    movq %rdx, %rax\n"
                                                                                         ::
                                                                                         Data.Text.Text)
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                           ("3:\n"
                                                                                            ::
                                                                                            Data.Text.Text)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                              ("    movq %rax, "
                                                                                               ::
                                                                                               Data.Text.Text)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                                 (d_reg'45'text_16
                                                                                                    (coe
                                                                                                       v1))
                                                                                                 ("\n"
                                                                                                  ::
                                                                                                  Data.Text.Text)))))))))))))))))))))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_52 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %rax\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    cqto\n" :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("    idivq " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_reg'45'text_16 (coe v3))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    movq %rax, " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_54 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %rax\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    cqto\n" :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("    idivq " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_reg'45'text_16 (coe v3))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    movq %rdx, " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_56 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) (", %rax\n" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit._.side-offset
d_side'45'offset_50 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_side'45'offset_50 ~v0 ~v1 v2 = du_side'45'offset_50 v2
du_side'45'offset_50 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_side'45'offset_50 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_24
        -> coe ("0" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_26
        -> coe ("8" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit._.walk-rax-rest
d_walk'45'rax'45'rest_52 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_walk'45'rax'45'rest_52 ~v0 ~v1 v2 v3
  = du_walk'45'rax'45'rest_52 v2 v3
du_walk'45'rax'45'rest_52 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_walk'45'rax'45'rest_52 v0 v1
  = case coe v1 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("    movq " :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (coe du_side'45'offset_50 (coe v2))
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(%rax), %rax\n" :: Data.Text.Text)
                           (coe du_walk'45'rax'45'rest_52 (coe v0) (coe v3)))) in
           coe
             (case coe v3 of
                []
                  -> coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("    movq " :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (coe du_side'45'offset_50 (coe v2))
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("(%rax), " :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (d_reg'45'text_16 (coe v0)) ("\n" :: Data.Text.Text))))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit._.path-load-text
d_path'45'load'45'text_66 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_path'45'load'45'text_66 ~v0 ~v1 v2 v3
  = du_path'45'load'45'text_66 v2 v3
du_path'45'load'45'text_66 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_path'45'load'45'text_66 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq %rdi, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v0)) ("\n" :: Data.Text.Text))
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("    movq " :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (coe du_side'45'offset_50 (coe v2))
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(%rdi), %rax\n" :: Data.Text.Text)
                           (coe du_walk'45'rax'45'rest_52 (coe v0) (coe v3)))) in
           coe
             (case coe v3 of
                []
                  -> coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("    movq " :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (coe du_side'45'offset_50 (coe v2))
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("(%rdi), " :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (d_reg'45'text_16 (coe v0)) ("\n" :: Data.Text.Text))))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit.program-text
d_program'45'text_120 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_28] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_program'45'text_120 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_instr'45'text_24 (coe v1)) (d_program'45'text_120 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit.emit-arith-block
d_emit'45'arith'45'block_128 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_126 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'block_128 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (":\n" :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("    subq $" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (coe
                  MAlonzo.Code.Data.Nat.Show.d_show_56
                  (mulInt
                     (coe (8 :: Integer))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_12
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.Compile.du_normalize_138
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_134
                              (coe v1))))))
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (", %rsp\n" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_program'45'text_120
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_480
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'abs_108
                              (coe
                                 MAlonzo.Code.Once.Arith.Machine.Compile.du_normalize_138
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_134
                                    (coe v1))))))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("    addq $" :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (coe
                              MAlonzo.Code.Data.Nat.Show.d_show_56
                              (mulInt
                                 (coe (8 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_12
                                    (coe
                                       MAlonzo.Code.Once.Arith.Machine.Compile.du_normalize_138
                                       (coe
                                          MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_134
                                          (coe v1))))))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (", %rsp\n" :: Data.Text.Text)
                              ("    ret\n\n" :: Data.Text.Text)))))))))
-- Once.Arith.Backend.X86-64.Emit.arith-block-symbol
d_arith'45'block'45'symbol_142 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_126 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_arith'45'block'45'symbol_142 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_56
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.du_block'45'name_278
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_134 (coe v0)))
-- Once.Arith.Backend.X86-64.Emit.emit-arith-blocks
d_emit'45'arith'45'blocks_146 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_126] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'blocks_146 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".globl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_arith'45'block'45'symbol_142 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_emit'45'arith'45'block_128
                         (coe d_arith'45'block'45'symbol_142 (coe v1)) (coe v1))
                      (d_emit'45'arith'45'blocks_146 (coe v2)))))
      _ -> MAlonzo.RTE.mazUnreachableError
