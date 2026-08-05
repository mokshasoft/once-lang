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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.CCC.Target.X86-64.Semantics.Word
d_Word_10 :: ()
d_Word_10 = erased
-- Once.CCC.Target.X86-64.Semantics.RegFile
d_RegFile_12 = ()
data T_RegFile_12
  = C_mkregfile_78 Integer Integer Integer Integer Integer Integer
                   Integer Integer Integer Integer Integer Integer Integer Integer
                   Integer Integer
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rax
d_get'45'rax_46 :: T_RegFile_12 -> Integer
d_get'45'rax_46 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rbx
d_get'45'rbx_48 :: T_RegFile_12 -> Integer
d_get'45'rbx_48 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rcx
d_get'45'rcx_50 :: T_RegFile_12 -> Integer
d_get'45'rcx_50 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rdx
d_get'45'rdx_52 :: T_RegFile_12 -> Integer
d_get'45'rdx_52 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rsi
d_get'45'rsi_54 :: T_RegFile_12 -> Integer
d_get'45'rsi_54 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rdi
d_get'45'rdi_56 :: T_RegFile_12 -> Integer
d_get'45'rdi_56 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rbp
d_get'45'rbp_58 :: T_RegFile_12 -> Integer
d_get'45'rbp_58 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-rsp
d_get'45'rsp_60 :: T_RegFile_12 -> Integer
d_get'45'rsp_60 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r8
d_get'45'r8_62 :: T_RegFile_12 -> Integer
d_get'45'r8_62 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r9
d_get'45'r9_64 :: T_RegFile_12 -> Integer
d_get'45'r9_64 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r10
d_get'45'r10_66 :: T_RegFile_12 -> Integer
d_get'45'r10_66 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r11
d_get'45'r11_68 :: T_RegFile_12 -> Integer
d_get'45'r11_68 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r12
d_get'45'r12_70 :: T_RegFile_12 -> Integer
d_get'45'r12_70 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r13
d_get'45'r13_72 :: T_RegFile_12 -> Integer
d_get'45'r13_72 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r14
d_get'45'r14_74 :: T_RegFile_12 -> Integer
d_get'45'r14_74 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.RegFile.get-r15
d_get'45'r15_76 :: T_RegFile_12 -> Integer
d_get'45'r15_76 v0
  = case coe v0 of
      C_mkregfile_78 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.readReg
d_readReg_80 ::
  T_RegFile_12 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer
d_readReg_80 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10
        -> coe d_get'45'rax_46 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12
        -> coe d_get'45'rbx_48 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rcx_14
        -> coe d_get'45'rcx_50 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdx_16
        -> coe d_get'45'rdx_52 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsi_18
        -> coe d_get'45'rsi_54 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20
        -> coe d_get'45'rdi_56 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22
        -> coe d_get'45'rbp_58 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24
        -> coe d_get'45'rsp_60 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r8_26
        -> coe d_get'45'r8_62 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r9_28
        -> coe d_get'45'r9_64 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r10_30
        -> coe d_get'45'r10_66 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r11_32
        -> coe d_get'45'r11_68 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34
        -> coe d_get'45'r12_70 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r13_36
        -> coe d_get'45'r13_72 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38
        -> coe d_get'45'r14_74 (coe v0)
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40
        -> coe d_get'45'r15_76 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.writeReg
d_writeReg_114 ::
  T_RegFile_12 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer -> T_RegFile_12
d_writeReg_114 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe v2) (coe d_get'45'rbx_48 (coe v0))
                  (coe d_get'45'rcx_50 (coe v0)) (coe d_get'45'rdx_52 (coe v0))
                  (coe d_get'45'rsi_54 (coe v0)) (coe d_get'45'rdi_56 (coe v0))
                  (coe d_get'45'rbp_58 (coe v0)) (coe d_get'45'rsp_60 (coe v0))
                  (coe d_get'45'r8_62 (coe v0)) (coe d_get'45'r9_64 (coe v0))
                  (coe d_get'45'r10_66 (coe v0)) (coe d_get'45'r11_68 (coe v0))
                  (coe d_get'45'r12_70 (coe v0)) (coe d_get'45'r13_72 (coe v0))
                  (coe d_get'45'r14_74 (coe v0)) (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0)) (coe v2)
                  (coe d_get'45'rcx_50 (coe v0)) (coe d_get'45'rdx_52 (coe v0))
                  (coe d_get'45'rsi_54 (coe v0)) (coe d_get'45'rdi_56 (coe v0))
                  (coe d_get'45'rbp_58 (coe v0)) (coe d_get'45'rsp_60 (coe v0))
                  (coe d_get'45'r8_62 (coe v0)) (coe d_get'45'r9_64 (coe v0))
                  (coe d_get'45'r10_66 (coe v0)) (coe d_get'45'r11_68 (coe v0))
                  (coe d_get'45'r12_70 (coe v0)) (coe d_get'45'r13_72 (coe v0))
                  (coe d_get'45'r14_74 (coe v0)) (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rcx_14
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe v2)
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdx_16
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe v2) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsi_18
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe v2)
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe v2) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbp_22
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe v2)
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe v2) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r8_26
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe v2)
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r9_28
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe v2) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r10_30
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe v2)
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r11_32
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe v2) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe v2)
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r13_36
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe v2) (coe d_get'45'r14_74 (coe v0))
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe v2)
                  (coe d_get'45'r15_76 (coe v0)))
      MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_78 (coe d_get'45'rax_46 (coe v0))
                  (coe d_get'45'rbx_48 (coe v0)) (coe d_get'45'rcx_50 (coe v0))
                  (coe d_get'45'rdx_52 (coe v0)) (coe d_get'45'rsi_54 (coe v0))
                  (coe d_get'45'rdi_56 (coe v0)) (coe d_get'45'rbp_58 (coe v0))
                  (coe d_get'45'rsp_60 (coe v0)) (coe d_get'45'r8_62 (coe v0))
                  (coe d_get'45'r9_64 (coe v0)) (coe d_get'45'r10_66 (coe v0))
                  (coe d_get'45'r11_68 (coe v0)) (coe d_get'45'r12_70 (coe v0))
                  (coe d_get'45'r13_72 (coe v0)) (coe d_get'45'r14_74 (coe v0))
                  (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.Memory
d_Memory_180 :: ()
d_Memory_180 = erased
-- Once.CCC.Target.X86-64.Semantics.readMem
d_readMem_182 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_182 v0 v1 = coe v0 v1
-- Once.CCC.Target.X86-64.Semantics.writeMem
d_writeMem_188 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_188 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Target.X86-64.Semantics.Flags
d_Flags_198 = ()
data T_Flags_198 = C_mkflags_212 Bool Bool Bool
-- Once.CCC.Target.X86-64.Semantics.Flags.zf
d_zf_206 :: T_Flags_198 -> Bool
d_zf_206 v0
  = case coe v0 of
      C_mkflags_212 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.Flags.cf
d_cf_208 :: T_Flags_198 -> Bool
d_cf_208 v0
  = case coe v0 of
      C_mkflags_212 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.Flags.sf
d_sf_210 :: T_Flags_198 -> Bool
d_sf_210 v0
  = case coe v0 of
      C_mkflags_212 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State
d_State_214 = ()
data T_State_214
  = C_mkstate_236 T_RegFile_12 (Integer -> Maybe Integer) T_Flags_198
                  Integer Bool
-- Once.CCC.Target.X86-64.Semantics.State.regs
d_regs_226 :: T_State_214 -> T_RegFile_12
d_regs_226 v0
  = case coe v0 of
      C_mkstate_236 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.memory
d_memory_228 :: T_State_214 -> Integer -> Maybe Integer
d_memory_228 v0
  = case coe v0 of
      C_mkstate_236 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.flags
d_flags_230 :: T_State_214 -> T_Flags_198
d_flags_230 v0
  = case coe v0 of
      C_mkstate_236 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.pc
d_pc_232 :: T_State_214 -> Integer
d_pc_232 v0
  = case coe v0 of
      C_mkstate_236 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.State.halted
d_halted_234 :: T_State_214 -> Bool
d_halted_234 v0
  = case coe v0 of
      C_mkstate_236 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.emptyMemory
d_emptyMemory_238 :: Integer -> Maybe Integer
d_emptyMemory_238 ~v0 = du_emptyMemory_238
du_emptyMemory_238 :: Maybe Integer
du_emptyMemory_238
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Target.X86-64.Semantics.initFlags
d_initFlags_242 :: T_Flags_198
d_initFlags_242
  = coe
      C_mkflags_212 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-64.Semantics.stack-top
d_stack'45'top_244
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Target.X86-64.Semantics.stack-top"
-- Once.CCC.Target.X86-64.Semantics.emptyRegFile
d_emptyRegFile_246 :: T_RegFile_12
d_emptyRegFile_246
  = coe
      C_mkregfile_78 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.initState
d_initState_248 :: T_State_214
d_initState_248
  = coe
      C_mkstate_236
      (coe
         d_writeReg_114 d_emptyRegFile_246
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
         d_stack'45'top_244)
      (\ v0 -> coe du_emptyMemory_238) (coe d_initFlags_242)
      (coe (0 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-64.Semantics.effectiveAddr
d_effectiveAddr_250 ::
  T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Mem_10 -> Integer
d_effectiveAddr_250 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base_12 v2
        -> coe d_readReg_80 (coe d_regs_226 (coe v0)) (coe v2)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_base'43'disp_14 v2 v3
        -> coe
             addInt (coe d_readReg_80 (coe d_regs_226 (coe v0)) (coe v2))
             (coe v3)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'disp_16 v2
        -> coe addInt (coe d_pc_232 (coe v0)) (coe v2)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rip'43'label_18 v2
        -> coe MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.readOperand
d_readOperand_270 ::
  T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Operand_20 ->
  Maybe Integer
d_readOperand_270 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe d_readReg_80 (coe d_regs_226 (coe v0)) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_24 v2
        -> coe
             d_readMem_182 (coe d_memory_228 (coe v0))
             (coe d_effectiveAddr_250 (coe v0) (coe v2))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.writeOperand
d_writeOperand_284 ::
  T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Operand_20 ->
  Integer -> T_State_214
d_writeOperand_284 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_236 (coe d_writeReg_114 (d_regs_226 (coe v0)) v2 v3)
                  (coe d_memory_228 (coe v0)) (coe d_flags_230 (coe v0))
                  (coe d_pc_232 (coe v0)) (coe d_halted_234 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mem_24 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkstate_236 (coe d_regs_226 (coe v0))
                  (coe
                     d_writeMem_188 (coe d_memory_228 (coe v0))
                     (coe d_effectiveAddr_250 (coe v0) (coe v2)) (coe v3))
                  (coe d_flags_230 (coe v0)) (coe d_pc_232 (coe v0))
                  (coe d_halted_234 (coe v0)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26 v2
        -> coe (\ v3 -> v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.updateFlags
d_updateFlags_300 :: Integer -> Integer -> T_Flags_198
d_updateFlags_300 v0 ~v1 = du_updateFlags_300 v0
du_updateFlags_300 :: Integer -> T_Flags_198
du_updateFlags_300 v0
  = coe
      C_mkflags_212 (coe eqInt (coe v0) (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.X86-64.Semantics._<ᵇ_
d__'60''7495'__304 :: Integer -> Integer -> Bool
d__'60''7495'__304 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d__'60''7495'__304 (coe v2) (coe v3)))
-- Once.CCC.Target.X86-64.Semantics.find-label-go
d_find'45'label'45'go_310 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer -> Maybe Integer
d_find'45'label'45'go_310 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v3 v4
        -> let v5
                 = d_find'45'label'45'go_310
                     (coe v0) (coe v4) (coe addInt (coe (1 :: Integer)) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_64 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7480'__224 (coe v6)
                          (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                       (coe
                          d_find'45'label'45'go_310 (coe v0) (coe v4)
                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.find-label
d_find'45'label_328 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 -> Maybe Integer
d_find'45'label_328 v0 v1
  = coe
      d_find'45'label'45'go_310 (coe v1) (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.X86-64.Semantics.execInstr
d_execInstr_334 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 ->
  Maybe T_State_214
d_execInstr_334 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_30 v3 v4
        -> let v5 = d_readOperand_270 (coe v1) (coe v4) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_236 (coe d_regs_226 (coe d_writeOperand_284 v1 v3 v6))
                          (coe d_memory_228 (coe d_writeOperand_284 v1 v3 v6))
                          (coe d_flags_230 (coe d_writeOperand_284 v1 v3 v6))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                          (coe d_halted_234 (coe d_writeOperand_284 v1 v3 v6)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_lea_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_236
                (coe
                   d_writeReg_114 (d_regs_226 (coe v1)) v3
                   (d_effectiveAddr_250 (coe v1) (coe v4)))
                (coe d_memory_228 (coe v1)) (coe d_flags_230 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                (coe d_halted_234 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_add_34 v3 v4
        -> let v5 = d_readOperand_270 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_270 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_236
                                    (coe
                                       d_regs_226
                                       (coe d_writeOperand_284 v1 v3 (addInt (coe v6) (coe v8))))
                                    (coe
                                       d_memory_228
                                       (coe d_writeOperand_284 v1 v3 (addInt (coe v6) (coe v8))))
                                    (coe du_updateFlags_300 (coe addInt (coe v6) (coe v8)))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                                    (coe
                                       d_halted_234
                                       (coe d_writeOperand_284 v1 v3 (addInt (coe v6) (coe v8)))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_36 v3 v4
        -> let v5 = d_readOperand_270 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_270 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_236
                                    (coe
                                       d_regs_226
                                       (coe
                                          d_writeOperand_284 v1 v3
                                          (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v6 v8)))
                                    (coe
                                       d_memory_228
                                       (coe
                                          d_writeOperand_284 v1 v3
                                          (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v6 v8)))
                                    (coe
                                       du_updateFlags_300
                                       (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v6 v8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                                    (coe
                                       d_halted_234
                                       (coe
                                          d_writeOperand_284 v1 v3
                                          (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v6 v8))))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_cmp_38 v3 v4
        -> let v5 = d_readOperand_270 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_270 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_236 (coe d_regs_226 (coe v1))
                                    (coe d_memory_228 (coe v1))
                                    (coe
                                       C_mkflags_212 (coe eqInt (coe v6) (coe v8))
                                       (coe d__'60''7495'__304 (coe v6) (coe v8))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                                    (coe d_halted_234 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_test_40 v3 v4
        -> let v5 = d_readOperand_270 (coe v1) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7 = d_readOperand_270 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_236 (coe d_regs_226 (coe v1))
                                    (coe d_memory_228 (coe v1))
                                    (coe
                                       C_mkflags_212 (coe eqInt (coe v6) (coe (0 :: Integer)))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                    (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                                    (coe d_halted_234 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jmp_42 v3
        -> let v4 = d_find'45'label_328 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_236 (coe d_regs_226 (coe v1)) (coe d_memory_228 (coe v1))
                          (coe d_flags_230 (coe v1)) (coe v5) (coe d_halted_234 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_236 (coe d_regs_226 (coe v1)) (coe d_memory_228 (coe v1))
                          (coe d_flags_230 (coe v1)) (coe d_pc_232 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_je_44 v3
        -> let v4 = d_zf_206 (coe d_flags_230 (coe v1)) in
           coe
             (if coe v4
                then let v5 = d_find'45'label_328 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_236 (coe d_regs_226 (coe v1))
                                    (coe d_memory_228 (coe v1)) (coe d_flags_230 (coe v1)) (coe v6)
                                    (coe d_halted_234 (coe v1)))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C_mkstate_236 (coe d_regs_226 (coe v1))
                                    (coe d_memory_228 (coe v1)) (coe d_flags_230 (coe v1))
                                    (coe d_pc_232 (coe v1)) (coe v4))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_236 (coe d_regs_226 (coe v1)) (coe d_memory_228 (coe v1))
                          (coe d_flags_230 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                          (coe d_halted_234 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_jne_46 v3
        -> let v4 = d_zf_206 (coe d_flags_230 (coe v1)) in
           coe
             (if coe v4
                then coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_236 (coe d_regs_226 (coe v1)) (coe d_memory_228 (coe v1))
                          (coe d_flags_230 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                          (coe d_halted_234 (coe v1)))
                else (let v5 = d_find'45'label_328 (coe v0) (coe v3) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     C_mkstate_236 (coe d_regs_226 (coe v1))
                                     (coe d_memory_228 (coe v1)) (coe d_flags_230 (coe v1)) (coe v6)
                                     (coe d_halted_234 (coe v1)))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     C_mkstate_236 (coe d_regs_226 (coe v1))
                                     (coe d_memory_228 (coe v1)) (coe d_flags_230 (coe v1))
                                     (coe d_pc_232 (coe v1))
                                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call_48 v3
        -> let v4 = d_readOperand_270 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_236
                          (coe
                             d_writeReg_114 (d_regs_226 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_80
                                   (coe d_regs_226 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80))
                          (coe
                             d_writeMem_188 (coe d_memory_228 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_80
                                   (coe d_regs_226 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
                             (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1))))
                          (coe d_flags_230 (coe v1)) (coe v5) (coe d_halted_234 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_50 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_236 (coe d_regs_226 (coe v1)) (coe d_memory_228 (coe v1))
                (coe d_flags_230 (coe v1)) (coe d_pc_232 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ret_52
        -> let v3
                 = d_readMem_182
                     (coe d_memory_228 (coe v1))
                     (coe
                        d_readReg_80 (coe d_regs_226 (coe v1))
                        (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_236
                          (coe
                             d_writeReg_114 (d_regs_226 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (addInt
                                (coe
                                   d_readReg_80 (coe d_regs_226 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)))
                          (coe d_memory_228 (coe v1)) (coe d_flags_230 (coe v1)) (coe v4)
                          (coe d_halted_234 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_push_54 v3
        -> let v4 = d_readOperand_270 (coe v1) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_236
                          (coe
                             d_writeReg_114 (d_regs_226 (coe v1))
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_80
                                   (coe d_regs_226 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80))
                          (coe
                             d_writeMem_188 (coe d_memory_228 (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                (d_readReg_80
                                   (coe d_regs_226 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)
                             (coe v5))
                          (coe d_flags_230 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                          (coe d_halted_234 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_pop_56 v3
        -> let v4
                 = d_readMem_182
                     (coe d_memory_228 (coe v1))
                     (coe
                        d_readReg_80 (coe d_regs_226 (coe v1))
                        (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_236
                          (coe
                             d_writeReg_114 (coe d_writeReg_114 (d_regs_226 (coe v1)) v3 v5)
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
                             (addInt
                                (coe
                                   d_readReg_80 (coe d_regs_226 (coe v1))
                                   (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_80)))
                          (coe d_memory_228 (coe v1)) (coe d_flags_230 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                          (coe d_halted_234 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_nop_58
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_236 (coe d_regs_226 (coe v1)) (coe d_memory_228 (coe v1))
                (coe d_flags_230 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                (coe d_halted_234 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_236 (coe d_regs_226 (coe v1)) (coe d_memory_228 (coe v1))
                (coe d_flags_230 (coe v1)) (coe d_pc_232 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_syscall_62
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_236 (coe d_regs_226 (coe v1)) (coe d_memory_228 (coe v1))
                (coe d_flags_230 (coe v1)) (coe d_pc_232 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_64 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_236 (coe d_regs_226 (coe v1)) (coe d_memory_228 (coe v1))
                (coe d_flags_230 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_232 (coe v1)))
                (coe d_halted_234 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.fetch
d_fetch_556 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28
d_fetch_556 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_fetch_556 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.step-not-halted
d_step'45'not'45'halted_564 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  T_State_214 -> Maybe T_State_214
d_step'45'not'45'halted_564 v0 v1
  = let v2 = d_fetch_556 (coe v0) (coe d_pc_232 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe d_execInstr_334 (coe v0) (coe v1) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_236 (coe d_regs_226 (coe v1)) (coe d_memory_228 (coe v1))
                   (coe d_flags_230 (coe v1)) (coe d_pc_232 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.X86-64.Semantics.step
d_step_574 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  T_State_214 -> Maybe T_State_214
d_step_574 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_halted_234 (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
      (coe d_step'45'not'45'halted_564 (coe v0) (coe v1))
-- Once.CCC.Target.X86-64.Semantics.exec
d_exec_580 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  T_State_214 -> Maybe T_State_214
d_exec_580 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_halted_234 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                (coe
                   d_exec'45'cont_582 (coe v3) (coe v1)
                   (coe d_step'45'not'45'halted_564 (coe v1) (coe v2))))
-- Once.CCC.Target.X86-64.Semantics.exec-cont
d_exec'45'cont_582 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Maybe T_State_214 -> Maybe T_State_214
d_exec'45'cont_582 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_halted_234 (coe v3)) (coe v2)
             (coe d_exec_580 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Semantics.defaultFuel
d_defaultFuel_598 :: Integer
d_defaultFuel_598 = coe (10000 :: Integer)
-- Once.CCC.Target.X86-64.Semantics.run
d_run_600 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  T_State_214 -> Maybe T_State_214
d_run_600 = coe d_exec_580 (coe d_defaultFuel_598)
