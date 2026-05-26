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

module MAlonzo.Code.Once.Arith.Backend.X86.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Arith.Backend.X86.CodeGen
import qualified MAlonzo.Code.Once.Arith.Backend.X86.Syntax
import qualified MAlonzo.Code.Once.Arith.Machine.Compile
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.Target.Symbol

-- Once.Arith.Backend.X86.Emit.reg-text
d_reg'45'text_10 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_reg'45'text_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_XR12_12
        -> coe ("%r12" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_XR13_14
        -> coe ("%r13" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_XR14_16
        -> coe ("%r14" :: Data.Text.Text)
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_XR15_18
        -> coe ("%r15" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.scratch-text
d_scratch'45'text_12 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_XScratch_20 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_scratch'45'text_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_mk'45'scratch_26 v1
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
-- Once.Arith.Backend.X86.Emit.instr-text
d_instr'45'text_16 ::
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_XInstr_28 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_instr'45'text_16 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_Xmov'45'imm_30 v1 v2
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
                      (d_reg'45'text_10 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_Xmov'45'rr_32 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_10 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_10 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_Xmov'45'r'45'm_34 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_10 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_scratch'45'text_12 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_Xmov'45'm'45'r_36 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_scratch'45'text_12 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_10 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_Xmov'45'arg_38 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("(%rdi), " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_10 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_Xadd'45'rr_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    addq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_10 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_10 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_Xsub'45'rr_42 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    subq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_10 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_10 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_Ximul'45'rr_44 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    imulq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_10 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (", " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_reg'45'text_10 (coe v1)) ("\n" :: Data.Text.Text))))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_Xneg'45'r_46 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    negq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_10 (coe v1)) ("\n" :: Data.Text.Text))
      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_Xmov'45'out_48 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("    movq " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_reg'45'text_10 (coe v1)) (", %rax\n" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.program-text
d_program'45'text_54 ::
  [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_XInstr_28] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_program'45'text_54 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_instr'45'text_16 (coe v1)) (d_program'45'text_54 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.Emit.emit-arith-block
d_emit'45'arith'45'block_62 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_86 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'block_62 v0 v1
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
                           MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_94 (coe v1)))))
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (", %rsp\n" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_program'45'text_54
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.X86.CodeGen.d_emit'45'program_368
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'abs_64
                              (coe
                                 MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_94 (coe v1)))))
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
                                       MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_94
                                       (coe v1)))))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (", %rsp\n" :: Data.Text.Text)
                              ("    ret\n\n" :: Data.Text.Text)))))))))
-- Once.Arith.Backend.X86.Emit.arith-block-symbol
d_arith'45'block'45'symbol_74 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_86 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_arith'45'block'45'symbol_74 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol_8
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.du_block'45'name_304
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_94 (coe v0)))
-- Once.Arith.Backend.X86.Emit.emit-arith-blocks
d_emit'45'arith'45'blocks_78 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_86] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emit'45'arith'45'blocks_78 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (".globl " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_arith'45'block'45'symbol_74 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\n" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_emit'45'arith'45'block_62
                         (coe d_arith'45'block'45'symbol_74 (coe v1)) (coe v1))
                      (d_emit'45'arith'45'blocks_78 (coe v2)))))
      _ -> MAlonzo.RTE.mazUnreachableError
