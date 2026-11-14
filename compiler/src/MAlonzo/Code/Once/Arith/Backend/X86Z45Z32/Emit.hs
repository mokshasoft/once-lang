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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.Compile
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Float.Word
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Theory
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
-- Once.Arith.Backend.X86-32.Emit.fcanon-32
d_fcanon'45'32_28 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fcanon'45'32_28 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    ucomiss " :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (", " :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  ("\n" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("    jnp " :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("f\n" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    movl $0x7fc00000, %eax\n" :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 ("    jmp " :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("f\n" :: Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             (":\n" :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                ("    movd " :: Data.Text.Text)
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      (", %eax\n" :: Data.Text.Text)
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         v2
                                                         (":\n" :: Data.Text.Text))))))))))))))))))
-- Once.Arith.Backend.X86-32.Emit.fkey-32
d_fkey'45'32_36 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fkey'45'32_36 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    testl %eax, %eax\n" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("    js " :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("f\n" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  ("    btcl $31, %eax\n" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("    jmp " :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("f\n" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (":\n" :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    ("    notl %eax\n" :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                       (":\n" :: Data.Text.Text))))))))))))
-- Once.Arith.Backend.X86-32.Emit.fload-32
d_fload'45'32_42 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fload'45'32_42 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    movd " :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (", %xmm0\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("    movd " :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                  (", %xmm1\n" :: Data.Text.Text)))))
-- Once.Arith.Backend.X86-32.Emit.fset-32
d_fset'45'32_48 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fset'45'32_48 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    movzbl %al, %eax\n" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("    movl %eax, " :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
            ("\n" :: Data.Text.Text)))
-- Once.Arith.Backend.X86-32.Emit.fstack-cmp-32
d_fstack'45'cmp'45'32_52 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fstack'45'cmp'45'32_52 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    cmpl (%esp), %eax\n" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("    " :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (" %al\n" :: Data.Text.Text)
               ("    addl $4, %esp\n" :: Data.Text.Text))))
-- Once.Arith.Backend.X86-32.Emit.forder-32
d_forder'45'32_56 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_forder'45'32_56 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_fload'45'32_42 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (d_fcanon'45'32_28
            (coe ("%xmm1" :: Data.Text.Text)) (coe ("1" :: Data.Text.Text))
            (coe ("2" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (d_fkey'45'32_36
               (coe ("3" :: Data.Text.Text)) (coe ("4" :: Data.Text.Text)))
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("    pushl %eax\n" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (d_fcanon'45'32_28
                     (coe ("%xmm0" :: Data.Text.Text)) (coe ("5" :: Data.Text.Text))
                     (coe ("6" :: Data.Text.Text)))
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_fkey'45'32_36
                        (coe ("7" :: Data.Text.Text)) (coe ("8" :: Data.Text.Text)))
                     (d_fstack'45'cmp'45'32_52 (coe v2)))))))
-- Once.Arith.Backend.X86-32.Emit.fident-32
d_fident'45'32_64 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fident'45'32_64 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_fload'45'32_42 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (d_fcanon'45'32_28
            (coe ("%xmm1" :: Data.Text.Text)) (coe ("1" :: Data.Text.Text))
            (coe ("2" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("    pushl %eax\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (d_fcanon'45'32_28
                  (coe ("%xmm0" :: Data.Text.Text)) (coe ("3" :: Data.Text.Text))
                  (coe ("4" :: Data.Text.Text)))
               (d_fstack'45'cmp'45'32_52 (coe v2)))))
-- Once.Arith.Backend.X86-32.Emit.fcmp-text-32
d_fcmp'45'text'45'32_78 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_FCmpOp_72 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fcmp'45'text'45'32_78 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Arith.CmpOp.C_fcmp_76 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Theory.C_float'45'rounded_118
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61''7496'_72
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'32_42 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomiss %xmm1, %xmm0\n    sete %al\n    setnp %ah\n    andb %ah, %al\n"
                               ::
                               Data.Text.Text)
                              (d_fset'45'32_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61''7496'_74
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'32_42 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomiss %xmm1, %xmm0\n    setne %al\n    setp %ah\n    orb %ah, %al\n"
                               ::
                               Data.Text.Text)
                              (d_fset'45'32_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60''7496'_76
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'32_42 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomiss %xmm0, %xmm1\n    seta %al\n" :: Data.Text.Text)
                              (d_fset'45'32_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61''7496'_78
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'32_42 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomiss %xmm0, %xmm1\n    setae %al\n" :: Data.Text.Text)
                              (d_fset'45'32_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62''7496'_80
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'32_42 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomiss %xmm1, %xmm0\n    seta %al\n" :: Data.Text.Text)
                              (d_fset'45'32_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61''7496'_82
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'32_42 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomiss %xmm1, %xmm0\n    setae %al\n" :: Data.Text.Text)
                              (d_fset'45'32_48 (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Theory.C_float'45'order_120
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60'_52
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_forder'45'32_56
                              (coe v2) (coe v3) (coe ("setb" :: Data.Text.Text)))
                           (d_fset'45'32_48 (coe v1))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61'_54
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_forder'45'32_56
                              (coe v2) (coe v3) (coe ("setbe" :: Data.Text.Text)))
                           (d_fset'45'32_48 (coe v1))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62'_56
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_forder'45'32_56
                              (coe v2) (coe v3) (coe ("seta" :: Data.Text.Text)))
                           (d_fset'45'32_48 (coe v1))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61'_58
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_forder'45'32_56
                              (coe v2) (coe v3) (coe ("setae" :: Data.Text.Text)))
                           (d_fset'45'32_48 (coe v1))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Theory.C_float'45'equality_122
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61'_60
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fident'45'32_64
                              (coe v2) (coe v3) (coe ("sete" :: Data.Text.Text)))
                           (d_fset'45'32_48 (coe v1))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61'_62
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fident'45'32_64
                              (coe v2) (coe v3) (coe ("setne" :: Data.Text.Text)))
                           (d_fset'45'32_48 (coe v1))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.arg-load-text
d_arg'45'load'45'text_152 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_arg'45'load'45'text_152 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl %ecx, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v0)) ("\n" :: Data.Text.Text))
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe
                   MAlonzo.Code.Data.Nat.Show.d_show_56
                   (mulInt (coe (4 :: Integer)) (coe v2)))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("(%ecx), " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v0)) ("\n" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.instr-text
d_instr'45'text_160 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instr'45'text_160 v0
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v1 v2 v3
        -> coe d_arg'45'load'45'text_152 (coe v1) (coe v2) (coe v3)
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xcmp'45'rrr_48 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmpl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v4))
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
                            ("    " :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (coe du_setcc_214 (coe v1))
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (" %al\n" :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("    movzbl %al, %eax\n" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        ("    movl %eax, " :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           (d_reg'45'text_16 (coe v2))
                                           ("\n" :: Data.Text.Text)))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_50 v1 v2 v3
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_52 v1 v2 v3
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_54 v1 v2 v3
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_56 v1 v2 v3
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_58 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_60 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_62 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_64 v1 v2 v3
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfcmp'45'rrr_66 v1 v2 v3 v4
        -> coe
             d_fcmp'45'text'45'32_78 (coe v1) (coe d_reg'45'text_16 (coe v2))
             (coe d_reg'45'text_16 (coe v3)) (coe d_reg'45'text_16 (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_68 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_70 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    xorl $-2147483648, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_72 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_74 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl $" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe
                   MAlonzo.Code.Data.Nat.Show.d_show_56
                   (MAlonzo.Code.Once.Float.Word.d_round_58
                      (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary32_50) (coe v2)))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_76 v1 v2 v3
        -> coe d_arg'45'load'45'text_152 (coe v1) (coe v2) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_78 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) (", %eax\n" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit._.setcc
d_setcc_214 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_setcc_214 ~v0 ~v1 ~v2 ~v3 v4 = du_setcc_214 v4
du_setcc_214 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_setcc_214 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'lt_8
        -> coe ("setl" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'le_10
        -> coe ("setle" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'gt_12
        -> coe ("setg" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ge_14
        -> coe ("setge" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'eq_16
        -> coe ("sete" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ne_18
        -> coe ("setne" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.program-text
d_program'45'text_296 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_program'45'text_296 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_instr'45'text_160 (coe v1)) (d_program'45'text_296 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.block-payload
d_block'45'payload_302 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'payload_302 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_72 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_946
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'abs_292
                          (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.Compile.du_normalize_322
                             (coe v3))))
                    (coe
                       MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_14
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.Compile.du_normalize_322 (coe v3)))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_946
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'abs_292
                          (coe v1) (coe v2) (coe v3)))
                    (coe
                       MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_14
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.emit-payload
d_emit'45'payload_316 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'payload_316 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
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
                                     (mulInt (coe (4 :: Integer)) (coe v3)))
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (", %esp\n" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (d_program'45'text_296 (coe v2))
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("    addl $" :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Show.d_show_56
                                                 (mulInt (coe (4 :: Integer)) (coe v3)))
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
                                                          ("    popl %esi\n" :: Data.Text.Text)
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             ("    popl %ebx\n" :: Data.Text.Text)
                                                             ("    ret\n\n"
                                                              ::
                                                              Data.Text.Text)))))))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.Emit.emit-arith-block
d_emit'45'arith'45'block_328 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'block_328 v0 v1
  = coe
      d_emit'45'payload_316 (coe v0)
      (coe d_block'45'payload_302 (coe v1))
-- Once.Arith.Backend.X86-32.Emit.arith-block-symbol
d_arith'45'block'45'symbol_334 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_arith'45'block'45'symbol_334 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_62
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.d_block'45'name_108
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'shape_66 (coe v0))
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'kind_68 (coe v0))
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_70 (coe v0)))
-- Once.Arith.Backend.X86-32.Emit.emit-arith-blocks
d_emit'45'arith'45'blocks_338 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'blocks_338 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".globl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_arith'45'block'45'symbol_334 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_emit'45'arith'45'block_328
                         (coe d_arith'45'block'45'symbol_334 (coe v1)) (coe v1))
                      (d_emit'45'arith'45'blocks_338 (coe v2)))))
      _ -> MAlonzo.RTE.mazUnreachableError
