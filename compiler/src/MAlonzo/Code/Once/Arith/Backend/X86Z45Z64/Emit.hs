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
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_scratch'45'text_20 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_mk'45'scratch_22 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe
                MAlonzo.Code.Data.Nat.Show.d_show_56
                (mulInt (coe (8 :: Integer)) (coe v1)))
             ("(%rsp)" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit.canon-nan-64
d_canon'45'nan'45'64_24 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_canon'45'nan'45'64_24 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    ucomisd %xmm0, %xmm0\n" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("    jnp 1f\n" :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("    pcmpeqd %xmm1, %xmm1\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("    psrlq $52, %xmm1\n" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  ("    psllq $51, %xmm1\n" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("    movapd %xmm1, %xmm0\n" :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("1:\n" :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("    movq %xmm0, " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                              ("\n" :: Data.Text.Text)))))))))
-- Once.Arith.Backend.X86-64.Emit.fcanon-64
d_fcanon'45'64_28 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fcanon'45'64_28 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    movq " :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (", " :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  ("\n" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("    ucomisd " :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (", " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 ("\n" :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    ("    jnp " :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("f\n" :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             ("    movabsq $0x7ff8000000000000, " :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   ("\n" :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      ("    jmp " :: Data.Text.Text)
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         v4
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            ("f\n" :: Data.Text.Text)
                                                            (coe
                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                               v3
                                                               (coe
                                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                  (":\n" :: Data.Text.Text)
                                                                  (coe
                                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                     ("    movq " :: Data.Text.Text)
                                                                     (coe
                                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                        v1
                                                                        (coe
                                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                           (", " :: Data.Text.Text)
                                                                           (coe
                                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                              v2
                                                                              (coe
                                                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                 ("\n"
                                                                                  ::
                                                                                  Data.Text.Text)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                    v4
                                                                                    (":\n"
                                                                                     ::
                                                                                     Data.Text.Text)))))))))))))))))))))))))))
-- Once.Arith.Backend.X86-64.Emit.fkey-64
d_fkey'45'64_40 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fkey'45'64_40 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    testq " :: Data.Text.Text)
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
                     ("    js " :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("f\n" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    btcq $63, " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    ("\n" :: Data.Text.Text)
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
                                                      ("    notq " :: Data.Text.Text)
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         v0
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            ("\n" :: Data.Text.Text)
                                                            (coe
                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                               v2
                                                               (":\n"
                                                                ::
                                                                Data.Text.Text))))))))))))))))))))
-- Once.Arith.Backend.X86-64.Emit.fset-64
d_fset'45'64_48 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fset'45'64_48 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    movzbq %al, %rax\n" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("    movq %rax, " :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
            ("\n" :: Data.Text.Text)))
-- Once.Arith.Backend.X86-64.Emit.fieee-64
d_fieee'45'64_52 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fieee'45'64_52 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    movq " :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (", %xmm0\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("    movq " :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                  (", %xmm1\n" :: Data.Text.Text)))))
-- Once.Arith.Backend.X86-64.Emit.forder-64
d_forder'45'64_58 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_forder'45'64_58 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_fcanon'45'64_28
         (coe v0) (coe ("%xmm0" :: Data.Text.Text))
         (coe ("%rax" :: Data.Text.Text)) (coe ("1" :: Data.Text.Text))
         (coe ("2" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (d_fkey'45'64_40
            (coe ("%rax" :: Data.Text.Text)) (coe ("3" :: Data.Text.Text))
            (coe ("4" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (d_fcanon'45'64_28
               (coe v1) (coe ("%xmm1" :: Data.Text.Text))
               (coe ("%rdx" :: Data.Text.Text)) (coe ("5" :: Data.Text.Text))
               (coe ("6" :: Data.Text.Text)))
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (d_fkey'45'64_40
                  (coe ("%rdx" :: Data.Text.Text)) (coe ("7" :: Data.Text.Text))
                  (coe ("8" :: Data.Text.Text)))
               ("    cmpq %rdx, %rax\n" :: Data.Text.Text))))
-- Once.Arith.Backend.X86-64.Emit.fident-64
d_fident'45'64_64 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fident'45'64_64 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_fcanon'45'64_28
         (coe v0) (coe ("%xmm0" :: Data.Text.Text))
         (coe ("%rax" :: Data.Text.Text)) (coe ("1" :: Data.Text.Text))
         (coe ("2" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (d_fcanon'45'64_28
            (coe v1) (coe ("%xmm1" :: Data.Text.Text))
            (coe ("%rdx" :: Data.Text.Text)) (coe ("3" :: Data.Text.Text))
            (coe ("4" :: Data.Text.Text)))
         ("    cmpq %rdx, %rax\n" :: Data.Text.Text))
-- Once.Arith.Backend.X86-64.Emit.fcmp-text-64
d_fcmp'45'text'45'64_76 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_FCmpOp_72 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fcmp'45'text'45'64_76 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Arith.CmpOp.C_fcmp_76 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Theory.C_float'45'rounded_118
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61''7496'_72
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fieee'45'64_52 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomisd %xmm1, %xmm0\n    sete %al\n    setnp %dl\n    andb %dl, %al\n"
                               ::
                               Data.Text.Text)
                              (d_fset'45'64_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61''7496'_74
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fieee'45'64_52 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomisd %xmm1, %xmm0\n    setne %al\n    setp %dl\n    orb %dl, %al\n"
                               ::
                               Data.Text.Text)
                              (d_fset'45'64_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60''7496'_76
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fieee'45'64_52 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomisd %xmm0, %xmm1\n    seta %al\n" :: Data.Text.Text)
                              (d_fset'45'64_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61''7496'_78
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fieee'45'64_52 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomisd %xmm0, %xmm1\n    setae %al\n" :: Data.Text.Text)
                              (d_fset'45'64_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62''7496'_80
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fieee'45'64_52 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomisd %xmm1, %xmm0\n    seta %al\n" :: Data.Text.Text)
                              (d_fset'45'64_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61''7496'_82
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fieee'45'64_52 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    ucomisd %xmm1, %xmm0\n    setae %al\n" :: Data.Text.Text)
                              (d_fset'45'64_48 (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Theory.C_float'45'order_120
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60'_52
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_forder'45'64_58 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    setb %al\n" :: Data.Text.Text) (d_fset'45'64_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61'_54
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_forder'45'64_58 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    setbe %al\n" :: Data.Text.Text) (d_fset'45'64_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62'_56
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_forder'45'64_58 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    seta %al\n" :: Data.Text.Text) (d_fset'45'64_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61'_58
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_forder'45'64_58 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    setae %al\n" :: Data.Text.Text) (d_fset'45'64_48 (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Theory.C_float'45'equality_122
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61'_60
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fident'45'64_64 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    sete %al\n" :: Data.Text.Text) (d_fset'45'64_48 (coe v1)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61'_62
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fident'45'64_64 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    setne %al\n" :: Data.Text.Text) (d_fset'45'64_48 (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit.arg-load-text
d_arg'45'load'45'text_150 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_arg'45'load'45'text_150 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq %rdi, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v0)) ("\n" :: Data.Text.Text))
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe
                   MAlonzo.Code.Data.Nat.Show.d_show_56
                   (mulInt (coe (8 :: Integer)) (coe v2)))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("(%rdi), " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v0)) ("\n" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit.instr-text
d_instr'45'text_158 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instr'45'text_158 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v1 v2 v3
        -> coe d_arg'45'load'45'text_150 (coe v1) (coe v2) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v1 v2
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    negq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v1 v2 v3
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v1 v2 v3
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xcmp'45'rrr_48 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cmpq " :: Data.Text.Text)
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
                               (coe du_setcc_212 (coe v1))
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (" %al\n" :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("    movzbq %al, %rax\n" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        ("    movq %rax, " :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           (d_reg'45'text_16 (coe v2))
                                           ("\n" :: Data.Text.Text)))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_50 v1 v2 v3
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_52 v1 v2 v3
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_54 v1 v2 v3
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
                      (d_reg'45'text_16 (coe v1))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("\n" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("    salq $" :: Data.Text.Text)
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
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %rax\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    sarq $63, %rax\n" :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("    shrq $" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (coe
                               MAlonzo.Code.Data.Nat.Show.d_show_56
                               (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (64 :: Integer) v3))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (", %rax\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    addq " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_reg'45'text_16 (coe v2))
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (", %rax\n" :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("    sarq $" :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 (", %rax\n" :: Data.Text.Text)
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("    movq %rax, " :: Data.Text.Text)
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       (d_reg'45'text_16 (coe v1))
                                                       ("\n" :: Data.Text.Text)))))))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_58 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movq " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %xmm1\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    addsd %xmm1, %xmm0\n" :: Data.Text.Text)
                               (d_canon'45'nan'45'64_24 (coe d_reg'45'text_16 (coe v1)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_60 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movq " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %xmm1\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    subsd %xmm1, %xmm0\n" :: Data.Text.Text)
                               (d_canon'45'nan'45'64_24 (coe d_reg'45'text_16 (coe v1)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_62 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movq " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %xmm1\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    mulsd %xmm1, %xmm0\n" :: Data.Text.Text)
                               (d_canon'45'nan'45'64_24 (coe d_reg'45'text_16 (coe v1)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_64 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movq " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v3))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %xmm1\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    divsd %xmm1, %xmm0\n" :: Data.Text.Text)
                               (d_canon'45'nan'45'64_24 (coe d_reg'45'text_16 (coe v1)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfcmp'45'rrr_66 v1 v2 v3 v4
        -> coe
             d_fcmp'45'text'45'64_76 (coe v1) (coe d_reg'45'text_16 (coe v2))
             (coe d_reg'45'text_16 (coe v3)) (coe d_reg'45'text_16 (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_68 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movq " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v1))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (", %xmm1\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    subsd %xmm1, %xmm0\n" :: Data.Text.Text)
                               (d_canon'45'nan'45'64_24 (coe d_reg'45'text_16 (coe v1)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_70 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    btcq $63, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_72 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    cvtsi2sdq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", %xmm0\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    movq %xmm0, " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text)))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_74 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movabsq $" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe
                   MAlonzo.Code.Data.Nat.Show.d_show_56
                   (MAlonzo.Code.Once.Float.Word.d_round_58
                      (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_52) (coe v2)))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_76 v1 v2 v3
        -> coe d_arg'45'load'45'text_150 (coe v1) (coe v2) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_78 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) (", %rax\n" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit._.setcc
d_setcc_212 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_setcc_212 ~v0 ~v1 ~v2 ~v3 v4 = du_setcc_212 v4
du_setcc_212 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_setcc_212 v0
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
-- Once.Arith.Backend.X86-64.Emit.program-text
d_program'45'text_294 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_program'45'text_294 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_instr'45'text_158 (coe v1)) (d_program'45'text_294 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit.block-payload
d_block'45'payload_300 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'payload_300 v0
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
-- Once.Arith.Backend.X86-64.Emit.emit-payload
d_emit'45'payload_314 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'payload_314 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
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
                         (mulInt (coe (8 :: Integer)) (coe v3)))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", %rsp\n" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_program'45'text_294 (coe v2))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    addq $" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (coe
                                     MAlonzo.Code.Data.Nat.Show.d_show_56
                                     (mulInt (coe (8 :: Integer)) (coe v3)))
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (", %rsp\n" :: Data.Text.Text)
                                     ("    ret\n\n" :: Data.Text.Text)))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.Emit.emit-arith-block
d_emit'45'arith'45'block_326 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'block_326 v0 v1
  = coe
      d_emit'45'payload_314 (coe v0)
      (coe d_block'45'payload_300 (coe v1))
-- Once.Arith.Backend.X86-64.Emit.arith-block-symbol
d_arith'45'block'45'symbol_332 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_arith'45'block'45'symbol_332 v0
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
-- Once.Arith.Backend.X86-64.Emit.emit-arith-blocks
d_emit'45'arith'45'blocks_336 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'blocks_336 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".globl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_arith'45'block'45'symbol_332 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_emit'45'arith'45'block_326
                         (coe d_arith'45'block'45'symbol_332 (coe v1)) (coe v1))
                      (d_emit'45'arith'45'blocks_336 (coe v2)))))
      _ -> MAlonzo.RTE.mazUnreachableError
