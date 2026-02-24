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

module MAlonzo.Code.Once.Backend.Assembler where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Base

-- Once.Backend.Assembler.Target
d_Target_6 = ()
data T_Target_6
  = C_C_8 | C_X86'45'64_10 | C_AArch64_12 | C_RiscV64_14
-- Once.Backend.Assembler.targetExtension
d_targetExtension_16 ::
  T_Target_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_targetExtension_16 v0
  = case coe v0 of
      C_C_8 -> coe (".c" :: Data.Text.Text)
      C_X86'45'64_10 -> coe (".s" :: Data.Text.Text)
      C_AArch64_12 -> coe (".s" :: Data.Text.Text)
      C_RiscV64_14 -> coe (".s" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.Assembler.commentPrefix
d_commentPrefix_18 ::
  T_Target_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_commentPrefix_18 v0
  = case coe v0 of
      C_C_8 -> coe ("// " :: Data.Text.Text)
      C_X86'45'64_10 -> coe ("# " :: Data.Text.Text)
      C_AArch64_12 -> coe ("// " :: Data.Text.Text)
      C_RiscV64_14 -> coe ("# " :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.Assembler.functionTypeDirective
d_functionTypeDirective_20 ::
  T_Target_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionTypeDirective_20 v0
  = let v1 = "@function" :: Data.Text.Text in
    coe
      (case coe v0 of
         C_AArch64_12 -> coe ("%function" :: Data.Text.Text)
         _ -> coe v1)
-- Once.Backend.Assembler.retInstr
d_retInstr_22 ::
  T_Target_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_retInstr_22 v0
  = case coe v0 of
      C_C_8 -> coe ("" :: Data.Text.Text)
      C_X86'45'64_10 -> coe ("    retq" :: Data.Text.Text)
      C_AArch64_12 -> coe ("    ret" :: Data.Text.Text)
      C_RiscV64_14 -> coe ("    ret" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.Assembler.InterpType
d_InterpType_24 = ()
data T_InterpType_24
  = C_InterpC_26 | C_InterpX86'45'64_28 | C_InterpAArch64_30 |
    C_InterpRiscV64_32
-- Once.Backend.Assembler.interpTypeExtension
d_interpTypeExtension_34 ::
  T_InterpType_24 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_interpTypeExtension_34 v0
  = case coe v0 of
      C_InterpC_26 -> coe (".c" :: Data.Text.Text)
      C_InterpX86'45'64_28 -> coe (".x86_64" :: Data.Text.Text)
      C_InterpAArch64_30 -> coe (".arm64" :: Data.Text.Text)
      C_InterpRiscV64_32 -> coe (".riscv64" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.Assembler.targetToInterp
d_targetToInterp_36 :: T_Target_6 -> T_InterpType_24
d_targetToInterp_36 v0
  = case coe v0 of
      C_C_8 -> coe C_InterpC_26
      C_X86'45'64_10 -> coe C_InterpX86'45'64_28
      C_AArch64_12 -> coe C_InterpAArch64_30
      C_RiscV64_14 -> coe C_InterpRiscV64_32
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.Assembler.unlines
d_unlines_38 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_unlines_38 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_unlines_38 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe v1
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.Assembler.concat
d_concat_46 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_concat_46
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe MAlonzo.Code.Data.String.Base.d__'43''43'__20)
      (coe ("" :: Data.Text.Text))
-- Once.Backend.Assembler.wrapFunction
d_wrapFunction_48 ::
  T_Target_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_wrapFunction_48 v0 v1 v2
  = coe
      d_unlines_38
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (".globl once_" :: Data.Text.Text) v1)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (".type once_" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (", " :: Data.Text.Text) (d_functionTypeDirective_20 (coe v0)))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  ("once_" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                     (":" :: Data.Text.Text)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe d_retInstr_22 (coe v0))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (".size once_" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (", .-once_" :: Data.Text.Text) v1)))
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
-- Once.Backend.Assembler.wrapLibrary
d_wrapLibrary_56 ::
  T_Target_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_wrapLibrary_56 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (d_commentPrefix_18 (coe v0))
            ("Generated by Once (verified via MAlonzo)" :: Data.Text.Text))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (".text" :: Data.Text.Text) ("\n\n" :: Data.Text.Text))))
      (coe
         d_concat_46
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               (\ v2 ->
                  case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_wrapFunction_48 (coe v0) (coe v3) (coe v4))
                           ("\n" :: Data.Text.Text)
                    _ -> MAlonzo.RTE.mazUnreachableError))
            (coe v1)))
-- Once.Backend.Assembler.startEntry
d_startEntry_72 ::
  T_Target_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_startEntry_72 v0
  = case coe v0 of
      C_C_8 -> coe ("" :: Data.Text.Text)
      C_X86'45'64_10
        -> coe
             d_unlines_38
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe ("" :: Data.Text.Text))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe ("# Entry point" :: Data.Text.Text))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe (".globl _start" :: Data.Text.Text))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe (".type _start, @function" :: Data.Text.Text))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe ("_start:" :: Data.Text.Text))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe ("    xorq %rdi, %rdi" :: Data.Text.Text))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("    call once_main" :: Data.Text.Text))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("    movq $60, %rax" :: Data.Text.Text))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe ("    xorq %rdi, %rdi" :: Data.Text.Text))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe ("    syscall" :: Data.Text.Text))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe (".size _start, .-_start" :: Data.Text.Text))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
      C_AArch64_12
        -> coe
             d_unlines_38
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe ("" :: Data.Text.Text))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe ("// Entry point" :: Data.Text.Text))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe (".globl _start" :: Data.Text.Text))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe (".type _start, %function" :: Data.Text.Text))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe ("_start:" :: Data.Text.Text))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe ("    mov x0, #0" :: Data.Text.Text))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("    bl once_main" :: Data.Text.Text))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("    mov x8, #93" :: Data.Text.Text))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe ("    mov x0, #0" :: Data.Text.Text))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe ("    svc #0" :: Data.Text.Text))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe (".size _start, .-_start" :: Data.Text.Text))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
      C_RiscV64_14
        -> coe
             d_unlines_38
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe ("" :: Data.Text.Text))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe ("# Entry point" :: Data.Text.Text))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe (".globl _start" :: Data.Text.Text))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe (".type _start, @function" :: Data.Text.Text))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe ("_start:" :: Data.Text.Text))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe ("    li a0, 0" :: Data.Text.Text))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("    call once_main" :: Data.Text.Text))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("    li a7, 93" :: Data.Text.Text))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe ("    li a0, 0" :: Data.Text.Text))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe ("    ecall" :: Data.Text.Text))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe (".size _start, .-_start" :: Data.Text.Text))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.Assembler.wrapExecutable
d_wrapExecutable_74 ::
  T_Target_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_wrapExecutable_74 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (d_commentPrefix_18 (coe v0))
            ("Generated by Once (verified via MAlonzo)" :: Data.Text.Text))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (".text" :: Data.Text.Text) ("\n\n" :: Data.Text.Text))))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe
            d_concat_46
            (coe
               MAlonzo.Code.Data.List.Base.du_map_22
               (coe
                  (\ v2 ->
                     case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                         -> coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_wrapFunction_48 (coe v0) (coe v3) (coe v4))
                              ("\n" :: Data.Text.Text)
                       _ -> MAlonzo.RTE.mazUnreachableError))
               (coe v1)))
         (d_startEntry_72 (coe v0)))
