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

module MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
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
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg

-- Once.Arith.Backend.X86-32.Emit.arith-reg
d_arith'45'reg_10 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8
d_arith'45'reg_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12
        -> coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edx_16
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14
        -> coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_edi_20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.arith-borrows
d_arith'45'borrows_14 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'borrows_14 = erased
-- Once.Arith.Backend.X86-32.Emit.reg-text
d_reg'45'text_16 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_reg'45'text_16 v0
  = coe
      MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.d_showReg_26
      (coe d_arith'45'reg_10 (coe v0))
-- Once.Arith.Backend.X86-32.Emit.scratch-text
d_scratch'45'text_20 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_scratch'45'text_20 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_mk'45'scratch_22 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe
                MAlonzo.Code.Data.Nat.Show.d_show_56
                (mulInt (coe (4 :: Integer)) (coe v1)))
             ("(%esp)" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.canon-nan-32
d_canon'45'nan'45'32_24 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_canon'45'nan'45'32_24 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    ucomiss %xmm0, %xmm0\n" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("    jnp 1f\n" :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("    pcmpeqd %xmm1, %xmm1\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("    psrld $23, %xmm1\n" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  ("    pslld $22, %xmm1\n" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("    movaps %xmm1, %xmm0\n" :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("1:\n" :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("    movd %xmm0, " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                              ("\n" :: Data.Text.Text)))))))))
-- Once.Arith.Backend.X86-32.Emit.instr-text
d_instr'45'text_28 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instr'45'text_28 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl $" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_scratch'45'text_20 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_scratch'45'text_20 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v1 v2
        -> coe du_path'45'load'45'text_74 (coe v1) (coe v2)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    imull " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    negl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    pushl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v3))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movl " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %eax\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    cmpl $0, (%esp)\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    jne 1f\n" :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("    movl $-1, %eax\n" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        ("    jmp 3f\n" :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("1:\n" :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("    cmpl $-1, (%esp)\n" :: Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 ("    jne 2f\n" :: Data.Text.Text)
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("    cmpl $0x80000000, %eax\n"
                                                     ::
                                                     Data.Text.Text)
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       ("    jne 2f\n" :: Data.Text.Text)
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          ("    movl $0x80000000, %eax\n"
                                                           ::
                                                           Data.Text.Text)
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             ("    jmp 3f\n" :: Data.Text.Text)
                                                             (coe
                                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                ("2:\n" :: Data.Text.Text)
                                                                (coe
                                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                   ("    cltd\n" :: Data.Text.Text)
                                                                   (coe
                                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                      ("    idivl (%esp)\n"
                                                                       ::
                                                                       Data.Text.Text)
                                                                      (coe
                                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                         ("3:\n" :: Data.Text.Text)
                                                                         (coe
                                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                            ("    addl $4, %esp\n"
                                                                             ::
                                                                             Data.Text.Text)
                                                                            (coe
                                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                               ("    movl %eax, "
                                                                                ::
                                                                                Data.Text.Text)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                  (d_reg'45'text_16
                                                                                     (coe v1))
                                                                                  ("\n"
                                                                                   ::
                                                                                   Data.Text.Text))))))))))))))))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    pushl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v3))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movl " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %eax\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    cmpl $0, (%esp)\n" :: Data.Text.Text)
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
                                           ("    cmpl $-1, (%esp)\n" :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("    jne 2f\n" :: Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 ("    cmpl $0x80000000, %eax\n" :: Data.Text.Text)
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("    jne 2f\n" :: Data.Text.Text)
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       ("    xorl %eax, %eax\n" :: Data.Text.Text)
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          ("    jmp 3f\n" :: Data.Text.Text)
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             ("2:\n" :: Data.Text.Text)
                                                             (coe
                                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                ("    cltd\n" :: Data.Text.Text)
                                                                (coe
                                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                   ("    idivl (%esp)\n"
                                                                    ::
                                                                    Data.Text.Text)
                                                                   (coe
                                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                      ("    movl %edx, %eax\n"
                                                                       ::
                                                                       Data.Text.Text)
                                                                      (coe
                                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                         ("3:\n" :: Data.Text.Text)
                                                                         (coe
                                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                            ("    addl $4, %esp\n"
                                                                             ::
                                                                             Data.Text.Text)
                                                                            (coe
                                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                               ("    movl %eax, "
                                                                                ::
                                                                                Data.Text.Text)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                  (d_reg'45'text_16
                                                                                     (coe v1))
                                                                                  ("\n"
                                                                                   ::
                                                                                   Data.Text.Text))))))))))))))))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    pushl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v3))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movl " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %eax\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    cltd\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    idivl (%esp)\n" :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("    addl $4, %esp\n" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        ("    movl %eax, " :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           (d_reg'45'text_16 (coe v1))
                                           ("\n" :: Data.Text.Text)))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    pushl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v3))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movl " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %eax\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    cltd\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    idivl (%esp)\n" :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("    movl %edx, %eax\n" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        ("    addl $4, %esp\n" :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("    movl %eax, " :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              (d_reg'45'text_16 (coe v1))
                                              ("\n" :: Data.Text.Text))))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("\n" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("    sall $" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (", " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %eax\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    sarl $31, %eax\n" :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("    shrl $" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (coe
                               MAlonzo.Code.Data.Nat.Show.d_show_56
                               (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (32 :: Integer) v3))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (", %eax\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    addl " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_reg'45'text_16 (coe v2))
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (", %eax\n" :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("    sarl $" :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 (", %eax\n" :: Data.Text.Text)
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("    movl %eax, " :: Data.Text.Text)
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       (d_reg'45'text_16 (coe v1))
                                                       ("\n" :: Data.Text.Text)))))))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_56 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movd " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %xmm1\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    addss %xmm1, %xmm0\n" :: Data.Text.Text)
                               (d_canon'45'nan'45'32_24 (coe d_reg'45'text_16 (coe v1)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_58 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movd " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %xmm1\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    subss %xmm1, %xmm0\n" :: Data.Text.Text)
                               (d_canon'45'nan'45'32_24 (coe d_reg'45'text_16 (coe v1)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_60 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movd " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %xmm1\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    mulss %xmm1, %xmm0\n" :: Data.Text.Text)
                               (d_canon'45'nan'45'32_24 (coe d_reg'45'text_16 (coe v1)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_62 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movd " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v3))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %xmm1\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    divss %xmm1, %xmm0\n" :: Data.Text.Text)
                               (d_canon'45'nan'45'32_24 (coe d_reg'45'text_16 (coe v1)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_64 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movd " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movd " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v1))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %xmm1\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    subss %xmm1, %xmm0\n" :: Data.Text.Text)
                               (d_canon'45'nan'45'32_24 (coe d_reg'45'text_16 (coe v1)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_66 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    xorl $-2147483648, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_68 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cvtsi2ssl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movd %xmm0, " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text)))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_70 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl $" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe
                   MAlonzo.Code.Data.Nat.Show.d_show_56
                   (MAlonzo.Code.Once.Float.Decimal.d_round_174
                      (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_40) (coe v2)))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_72 v1 v2
        -> coe
             d_instr'45'text_28
             (coe
                MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34
                (coe v1) (coe v2))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_74 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) (", %eax\n" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit._.side-offset
d_side'45'offset_58 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_side'45'offset_58 ~v0 ~v1 v2 = du_side'45'offset_58 v2
du_side'45'offset_58 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_side'45'offset_58 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
        -> coe ("0" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
        -> coe ("4" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit._.walk-eax-rest
d_walk'45'eax'45'rest_60 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_walk'45'eax'45'rest_60 ~v0 ~v1 v2 v3
  = du_walk'45'eax'45'rest_60 v2 v3
du_walk'45'eax'45'rest_60 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_walk'45'eax'45'rest_60 v0 v1
  = case coe v1 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("    movl " :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (coe du_side'45'offset_58 (coe v2))
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(%eax), %eax\n" :: Data.Text.Text)
                           (coe du_walk'45'eax'45'rest_60 (coe v0) (coe v3)))) in
           coe
             (case coe v3 of
                []
                  -> coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("    movl " :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (coe du_side'45'offset_58 (coe v2))
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("(%eax), " :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (d_reg'45'text_16 (coe v0)) ("\n" :: Data.Text.Text))))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit._.path-load-text
d_path'45'load'45'text_74 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_path'45'load'45'text_74 ~v0 ~v1 v2 v3
  = du_path'45'load'45'text_74 v2 v3
du_path'45'load'45'text_74 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_path'45'load'45'text_74 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl %ecx, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v0)) ("\n" :: Data.Text.Text))
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("    movl " :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (coe du_side'45'offset_58 (coe v2))
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(%ecx), %eax\n" :: Data.Text.Text)
                           (coe du_walk'45'eax'45'rest_60 (coe v0) (coe v3)))) in
           coe
             (case coe v3 of
                []
                  -> coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("    movl " :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (coe du_side'45'offset_58 (coe v2))
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("(%ecx), " :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (d_reg'45'text_16 (coe v0)) ("\n" :: Data.Text.Text))))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.program-text
d_program'45'text_172 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_program'45'text_172 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_instr'45'text_28 (coe v1)) (d_program'45'text_172 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.emit-arith-block
d_emit'45'arith'45'block_180 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_144 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'block_180 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_158 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (":\n" :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("    pushl %ebx\n" :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("    pushl %esi\n" :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("    pushl %edx\n" :: Data.Text.Text)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   ("    pushl %edi\n" :: Data.Text.Text)
                                   (coe
                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                      ("    subl $" :: Data.Text.Text)
                                      (coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                         (coe
                                            MAlonzo.Code.Data.Nat.Show.d_show_56
                                            (mulInt
                                               (coe (4 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_14
                                                  (coe
                                                     MAlonzo.Code.Once.Arith.Machine.Compile.du_normalize_298
                                                     (coe v4)))))
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            (", %esp\n" :: Data.Text.Text)
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               (d_program'45'text_172
                                                  (coe
                                                     MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_870
                                                     (coe
                                                        MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'abs_268
                                                        (coe v3)
                                                        (coe
                                                           MAlonzo.Code.Once.Arith.Machine.Compile.du_normalize_298
                                                           (coe v4)))))
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  ("    addl $" :: Data.Text.Text)
                                                  (coe
                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Show.d_show_56
                                                        (mulInt
                                                           (coe (4 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_14
                                                              (coe
                                                                 MAlonzo.Code.Once.Arith.Machine.Compile.du_normalize_298
                                                                 (coe v4)))))
                                                     (coe
                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                        (", %esp\n" :: Data.Text.Text)
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           ("    popl %edi\n" :: Data.Text.Text)
                                                           (coe
                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                              ("    popl %edx\n" :: Data.Text.Text)
                                                              (coe
                                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                 ("    popl %esi\n"
                                                                  ::
                                                                  Data.Text.Text)
                                                                 (coe
                                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                    ("    popl %ebx\n"
                                                                     ::
                                                                     Data.Text.Text)
                                                                    ("    ret\n\n"
                                                                     ::
                                                                     Data.Text.Text)))))))))))))))))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (":\n" :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("    pushl %ebx\n" :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("    pushl %esi\n" :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("    pushl %edx\n" :: Data.Text.Text)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   ("    pushl %edi\n" :: Data.Text.Text)
                                   (coe
                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                      ("    subl $" :: Data.Text.Text)
                                      (coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                         (coe
                                            MAlonzo.Code.Data.Nat.Show.d_show_56
                                            (mulInt
                                               (coe (4 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_14
                                                  (coe v4))))
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            (", %esp\n" :: Data.Text.Text)
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               (d_program'45'text_172
                                                  (coe
                                                     MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_870
                                                     (coe
                                                        MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'abs_268
                                                        (coe v3) (coe v4))))
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  ("    addl $" :: Data.Text.Text)
                                                  (coe
                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Show.d_show_56
                                                        (mulInt
                                                           (coe (4 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_14
                                                              (coe v4))))
                                                     (coe
                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                        (", %esp\n" :: Data.Text.Text)
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           ("    popl %edi\n" :: Data.Text.Text)
                                                           (coe
                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                              ("    popl %edx\n" :: Data.Text.Text)
                                                              (coe
                                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                 ("    popl %esi\n"
                                                                  ::
                                                                  Data.Text.Text)
                                                                 (coe
                                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                    ("    popl %ebx\n"
                                                                     ::
                                                                     Data.Text.Text)
                                                                    ("    ret\n\n"
                                                                     ::
                                                                     Data.Text.Text)))))))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.arith-block-symbol
d_arith'45'block'45'symbol_210 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_144 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_arith'45'block'45'symbol_210 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_56
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.du_block'45'name_342
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_156 (coe v0)))
-- Once.Arith.Backend.X86-32.Emit.emit-arith-blocks
d_emit'45'arith'45'blocks_214 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_144] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'blocks_214 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".globl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_arith'45'block'45'symbol_210 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_emit'45'arith'45'block_180
                         (coe d_arith'45'block'45'symbol_210 (coe v1)) (coe v1))
                      (d_emit'45'arith'45'blocks_214 (coe v2)))))
      _ -> MAlonzo.RTE.mazUnreachableError
