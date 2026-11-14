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

module MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit where

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
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Once.Target.Symbol

-- Once.Arith.Backend.RiscV64.Emit.arith-reg
d_arith'45'reg_10 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_arith'45'reg_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12
        -> coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a3_24
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14
        -> coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a4_26
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV64.Emit.arith-disjoint
d_arith'45'disjoint_14 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'disjoint_14 = erased
-- Once.Arith.Backend.RiscV64.Emit.reg-text
d_reg'45'text_16 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_reg'45'text_16 v0
  = coe
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.d_showReg_52
      (coe d_arith'45'reg_10 (coe v0))
-- Once.Arith.Backend.RiscV64.Emit.scratch-text
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
             ("(sp)" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV64.Emit.fcanon-rv
d_fcanon'45'rv_24 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fcanon'45'rv_24 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    feq.d " :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (", " :: Data.Text.Text)
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
                           ("    bnez " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (", " :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("f\n" :: Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("    li a0, 0x7ff8000000000000\n" :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             ("    j " :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   ("f\n" :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      v2
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         (":\n" :: Data.Text.Text)
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            ("    fmv.x.d a0, " :: Data.Text.Text)
                                                            (coe
                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                               v1
                                                               (coe
                                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                  ("\n" :: Data.Text.Text)
                                                                  (coe
                                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                     v3
                                                                     (":\n"
                                                                      ::
                                                                      Data.Text.Text))))))))))))))))))))))
-- Once.Arith.Backend.RiscV64.Emit.fkey-rv
d_fkey'45'rv_34 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fkey'45'rv_34 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    srai " :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (", a0, 63\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("    srli " :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (", " :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (", 1\n" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    xor a0, a0, " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                                 ("\n" :: Data.Text.Text))))))))))
-- Once.Arith.Backend.RiscV64.Emit.fload-rv
d_fload'45'rv_38 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fload'45'rv_38 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("    fmv.d.x ft0, " :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("    fmv.d.x ft1, " :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                  ("\n" :: Data.Text.Text)))))
-- Once.Arith.Backend.RiscV64.Emit.fkeys-rv
d_fkeys'45'rv_44 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fkeys'45'rv_44 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_fload'45'rv_38 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (d_fcanon'45'rv_24
            (coe v0) (coe ("ft1" :: Data.Text.Text))
            (coe ("1" :: Data.Text.Text)) (coe ("2" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (d_fkey'45'rv_34 (coe v0))
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("    fmv.d.x ft1, a0\n" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (d_fcanon'45'rv_24
                     (coe v0) (coe ("ft0" :: Data.Text.Text))
                     (coe ("3" :: Data.Text.Text)) (coe ("4" :: Data.Text.Text)))
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_fkey'45'rv_34 (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("    fmv.x.d " :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                           (", ft1\n" :: Data.Text.Text))))))))
-- Once.Arith.Backend.RiscV64.Emit.fcanons-rv
d_fcanons'45'rv_52 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fcanons'45'rv_52 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_fload'45'rv_38 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (d_fcanon'45'rv_24
            (coe v0) (coe ("ft1" :: Data.Text.Text))
            (coe ("1" :: Data.Text.Text)) (coe ("2" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("    fmv.d.x ft1, a0\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (d_fcanon'45'rv_24
                  (coe v0) (coe ("ft0" :: Data.Text.Text))
                  (coe ("3" :: Data.Text.Text)) (coe ("4" :: Data.Text.Text)))
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  ("    fmv.x.d " :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                     (", ft1\n" :: Data.Text.Text))))))
-- Once.Arith.Backend.RiscV64.Emit.fcmp-text-rv
d_fcmp'45'text'45'rv_66 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_FCmpOp_72 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fcmp'45'text'45'rv_66 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Arith.CmpOp.C_fcmp_76 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Theory.C_float'45'rounded_118
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61''7496'_72
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'rv_38 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    feq.d " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (", ft0, ft1\n" :: Data.Text.Text)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61''7496'_74
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'rv_38 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    feq.d " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (", ft0, ft1\n" :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("    xori " :: Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             (", " :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                                (", 1\n" :: Data.Text.Text))))))))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60''7496'_76
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'rv_38 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    flt.d " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (", ft0, ft1\n" :: Data.Text.Text)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61''7496'_78
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'rv_38 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    fle.d " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (", ft0, ft1\n" :: Data.Text.Text)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62''7496'_80
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'rv_38 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    flt.d " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (", ft1, ft0\n" :: Data.Text.Text)))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61''7496'_82
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fload'45'rv_38 (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    fle.d " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (", ft1, ft0\n" :: Data.Text.Text)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Theory.C_float'45'order_120
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60'_52
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fkeys'45'rv_44 (coe v1) (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    slt " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (", a0, " :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                       ("\n" :: Data.Text.Text)))))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''60''61'_54
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fkeys'45'rv_44 (coe v1) (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    slt " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (", " :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          (", a0\n" :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             ("    xori " :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   (", " :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      v1 (", 1\n" :: Data.Text.Text))))))))))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62'_56
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fkeys'45'rv_44 (coe v1) (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    slt " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (", " :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                       (", a0\n" :: Data.Text.Text)))))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''62''61'_58
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fkeys'45'rv_44 (coe v1) (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    slt " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (", a0, " :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("\n" :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             ("    xori " :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   (", " :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      v1 (", 1\n" :: Data.Text.Text))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Theory.C_float'45'equality_122
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''61''61'_60
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fcanons'45'rv_52 (coe v1) (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    xor " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (", a0, " :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("\n" :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             ("    seqz " :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   (", " :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      v1 ("\n" :: Data.Text.Text))))))))))
                    MAlonzo.Code.Once.Spec.Theory.C_'8245''33''61'_62
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_fcanons'45'rv_52 (coe v1) (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("    xor " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (", a0, " :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("\n" :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             ("    snez " :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   (", " :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      v1 ("\n" :: Data.Text.Text))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV64.Emit.arg-load-text
d_arg'45'load'45'text_140 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_arg'45'load'45'text_140 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mv " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v0)) (", t0\n" :: Data.Text.Text))
      (:) v3 v4
        -> let v5
                 = ltInt
                     (coe addInt (coe mulInt (coe (7 :: Integer)) (coe v2)) (coe v2))
                     (coe (2048 :: Integer)) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("    ld " :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (d_reg'45'text_16 (coe v0))
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (", " :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (coe
                                   MAlonzo.Code.Data.Nat.Show.d_show_56
                                   (mulInt (coe (8 :: Integer)) (coe v2)))
                                ("(t0)\n" :: Data.Text.Text))))
                else coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("    li " :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (d_reg'45'text_16 (coe v0))
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (", " :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (coe
                                   MAlonzo.Code.Data.Nat.Show.d_show_56
                                   (mulInt (coe (8 :: Integer)) (coe v2)))
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   ("\n" :: Data.Text.Text)
                                   (coe
                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                      ("    add " :: Data.Text.Text)
                                      (coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                         (d_reg'45'text_16 (coe v0))
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            (", " :: Data.Text.Text)
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               (d_reg'45'text_16 (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  (", t0\n" :: Data.Text.Text)
                                                  (coe
                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                     ("    ld " :: Data.Text.Text)
                                                     (coe
                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                        (d_reg'45'text_16 (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           (", 0(" :: Data.Text.Text)
                                                           (coe
                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                              (d_reg'45'text_16 (coe v0))
                                                              (")\n"
                                                               ::
                                                               Data.Text.Text)))))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV64.Emit.instr-text
d_instr'45'text_160 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instr'45'text_160 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    li " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                      ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mv " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v2)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sd " :: Data.Text.Text)
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
             ("    ld " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_scratch'45'text_20 (coe v2)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v1 v2 v3
        -> coe d_arg'45'load'45'text_140 (coe v1) (coe v2) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    add " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_reg'45'text_16 (coe v2)) ("\n" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    sub " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_reg'45'text_16 (coe v2)) ("\n" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mul " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_reg'45'text_16 (coe v2)) ("\n" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    neg " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    div " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_reg'45'text_16 (coe v3)) ("\n" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    rem " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_reg'45'text_16 (coe v3)) ("\n" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xcmp'45'rrr_48 v1 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.CmpOp.C_c'45'lt_8
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    slt " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_reg'45'text_16 (coe v2))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (", " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (d_reg'45'text_16 (coe v3))
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (", " :: Data.Text.Text)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (d_reg'45'text_16 (coe v4)) ("\n" :: Data.Text.Text))))))
             MAlonzo.Code.Once.Arith.CmpOp.C_c'45'le_10
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    slt " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_reg'45'text_16 (coe v2))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (", " :: Data.Text.Text)
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
                                         ("    xori " :: Data.Text.Text)
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            (d_reg'45'text_16 (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               (", " :: Data.Text.Text)
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  (d_reg'45'text_16 (coe v2))
                                                  (", 1\n" :: Data.Text.Text)))))))))))
             MAlonzo.Code.Once.Arith.CmpOp.C_c'45'gt_12
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    slt " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_reg'45'text_16 (coe v2))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (", " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (d_reg'45'text_16 (coe v4))
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (", " :: Data.Text.Text)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (d_reg'45'text_16 (coe v3)) ("\n" :: Data.Text.Text))))))
             MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ge_14
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    slt " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_reg'45'text_16 (coe v2))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (", " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (d_reg'45'text_16 (coe v3))
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (", " :: Data.Text.Text)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (d_reg'45'text_16 (coe v4))
                                   (coe
                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                      ("\n" :: Data.Text.Text)
                                      (coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                         ("    xori " :: Data.Text.Text)
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            (d_reg'45'text_16 (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               (", " :: Data.Text.Text)
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  (d_reg'45'text_16 (coe v2))
                                                  (", 1\n" :: Data.Text.Text)))))))))))
             MAlonzo.Code.Once.Arith.CmpOp.C_c'45'eq_16
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    sub " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_reg'45'text_16 (coe v2))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (", " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (d_reg'45'text_16 (coe v3))
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (", " :: Data.Text.Text)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (d_reg'45'text_16 (coe v4))
                                   (coe
                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                      ("\n" :: Data.Text.Text)
                                      (coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                         ("    seqz " :: Data.Text.Text)
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            (d_reg'45'text_16 (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               (", " :: Data.Text.Text)
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  (d_reg'45'text_16 (coe v2))
                                                  ("\n" :: Data.Text.Text)))))))))))
             MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ne_18
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("    sub " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_reg'45'text_16 (coe v2))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (", " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (d_reg'45'text_16 (coe v3))
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (", " :: Data.Text.Text)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (d_reg'45'text_16 (coe v4))
                                   (coe
                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                      ("\n" :: Data.Text.Text)
                                      (coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                         ("    snez " :: Data.Text.Text)
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            (d_reg'45'text_16 (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               (", " :: Data.Text.Text)
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  (d_reg'45'text_16 (coe v2))
                                                  ("\n" :: Data.Text.Text)))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_50 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    div " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_reg'45'text_16 (coe v3)) ("\n" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_52 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    rem " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_reg'45'text_16 (coe v3)) ("\n" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_54 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    slli " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_16 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (", " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                            ("\n" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_56 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    srai a0, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", 63\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    srli a0, a0, " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (coe
                            MAlonzo.Code.Data.Nat.Show.d_show_56
                            (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (64 :: Integer) v3))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    add a0, " :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (d_reg'45'text_16 (coe v2))
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (", a0\n" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        ("    srai " :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           (d_reg'45'text_16 (coe v1))
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              (", a0, " :: Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                                                 ("\n" :: Data.Text.Text)))))))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_58 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmv.d.x ft0, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    fmv.d.x ft1, " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    fadd.d ft0, ft0, ft1\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    fmv.x.d " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_reg'45'text_16 (coe v1))
                                     (", ft0\n" :: Data.Text.Text)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_60 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmv.d.x ft0, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    fmv.d.x ft1, " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    fsub.d ft0, ft0, ft1\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    fmv.x.d " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_reg'45'text_16 (coe v1))
                                     (", ft0\n" :: Data.Text.Text)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_62 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmv.d.x ft0, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    fmv.d.x ft1, " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v2))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    fmul.d ft0, ft0, ft1\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    fmv.x.d " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_reg'45'text_16 (coe v1))
                                     (", ft0\n" :: Data.Text.Text)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_64 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmv.d.x ft0, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    fmv.d.x ft1, " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v3))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    fdiv.d ft0, ft0, ft1\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    fmv.x.d " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_reg'45'text_16 (coe v1))
                                     (", ft0\n" :: Data.Text.Text)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfcmp'45'rrr_66 v1 v2 v3 v4
        -> coe
             d_fcmp'45'text'45'rv_66 (coe v1) (coe d_reg'45'text_16 (coe v2))
             (coe d_reg'45'text_16 (coe v3)) (coe d_reg'45'text_16 (coe v4))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_68 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmv.d.x ft0, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    fmv.d.x ft1, " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v1))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("\n" :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    fsub.d ft0, ft0, ft1\n" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("    fmv.x.d " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_reg'45'text_16 (coe v1))
                                     (", ft0\n" :: Data.Text.Text)))))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_70 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fmv.d.x ft0, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    fneg.d ft0, ft0\n" :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("    fmv.x.d " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_reg'45'text_16 (coe v1)) (", ft0\n" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_72 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    fcvt.d.l ft0, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("    fmv.x.d " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (d_reg'45'text_16 (coe v1)) (", ft0\n" :: Data.Text.Text)))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_74 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    li " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe
                         MAlonzo.Code.Data.Nat.Show.d_show_56
                         (MAlonzo.Code.Once.Float.Word.d_round_58
                            (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_52) (coe v2)))
                      ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_76 v1 v2 v3
        -> coe d_arg'45'load'45'text_140 (coe v1) (coe v2) (coe v3)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_78 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    mv a0, " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_16 (coe v1)) ("\n" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV64.Emit.program-text
d_program'45'text_318 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_program'45'text_318 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_instr'45'text_160 (coe v1)) (d_program'45'text_318 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV64.Emit.block-payload
d_block'45'payload_324 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'payload_324 v0
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
-- Once.Arith.Backend.RiscV64.Emit.emit-payload
d_emit'45'payload_338 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'payload_338 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (":\n" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("    addi sp, sp, -" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe
                         MAlonzo.Code.Data.Nat.Show.d_show_56
                         (mulInt (coe (8 :: Integer)) (coe v3)))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("\n" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_program'45'text_318 (coe v2))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("    addi sp, sp, " :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (coe
                                     MAlonzo.Code.Data.Nat.Show.d_show_56
                                     (mulInt (coe (8 :: Integer)) (coe v3)))
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("\n" :: Data.Text.Text)
                                     ("    ret\n\n" :: Data.Text.Text)))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RiscV64.Emit.emit-arith-block
d_emit'45'arith'45'block_350 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'block_350 v0 v1
  = coe
      d_emit'45'payload_338 (coe v0)
      (coe d_block'45'payload_324 (coe v1))
-- Once.Arith.Backend.RiscV64.Emit.arith-block-symbol
d_arith'45'block'45'symbol_356 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_arith'45'block'45'symbol_356 v0
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
-- Once.Arith.Backend.RiscV64.Emit.emit-arith-blocks
d_emit'45'arith'45'blocks_360 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'blocks_360 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".globl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_arith'45'block'45'symbol_356 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_emit'45'arith'45'block_350
                         (coe d_arith'45'block'45'symbol_356 (coe v1)) (coe v1))
                      (d_emit'45'arith'45'blocks_360 (coe v2)))))
      _ -> MAlonzo.RTE.mazUnreachableError
