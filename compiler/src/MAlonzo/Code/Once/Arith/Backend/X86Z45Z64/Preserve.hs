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

module MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Preserve where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.Arith.Backend.PreserveCore
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Confine
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.Arith.Backend.X86-64.Preserve.AgreeCCC
d_AgreeCCC_14 a0 a1 = ()
data T_AgreeCCC_14 = C_mkAgree_48
-- Once.Arith.Backend.X86-64.Preserve.AgreeCCC.a-rcx
d_a'45'rcx_34 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'rcx_34 = erased
-- Once.Arith.Backend.X86-64.Preserve.AgreeCCC.a-rbx
d_a'45'rbx_36 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'rbx_36 = erased
-- Once.Arith.Backend.X86-64.Preserve.AgreeCCC.a-rbp
d_a'45'rbp_38 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'rbp_38 = erased
-- Once.Arith.Backend.X86-64.Preserve.AgreeCCC.a-rsi
d_a'45'rsi_40 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'rsi_40 = erased
-- Once.Arith.Backend.X86-64.Preserve.AgreeCCC.a-rsp
d_a'45'rsp_42 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'rsp_42 = erased
-- Once.Arith.Backend.X86-64.Preserve.AgreeCCC.a-r12
d_a'45'r12_44 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'r12_44 = erased
-- Once.Arith.Backend.X86-64.Preserve.AgreeCCC.a-r15
d_a'45'r15_46 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'r15_46 = erased
-- Once.Arith.Backend.X86-64.Preserve.agree-refl-ccc
d_agree'45'refl'45'ccc_52 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  T_AgreeCCC_14
d_agree'45'refl'45'ccc_52 = erased
-- Once.Arith.Backend.X86-64.Preserve.write-nonccc-agrees
d_write'45'nonccc'45'agrees_62 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_AgreeCCC_14
d_write'45'nonccc'45'agrees_62 = erased
-- Once.Arith.Backend.X86-64.Preserve.AgreeCCC-trans
d_AgreeCCC'45'trans_148 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  T_AgreeCCC_14 -> T_AgreeCCC_14 -> T_AgreeCCC_14
d_AgreeCCC'45'trans_148 = erased
-- Once.Arith.Backend.X86-64.Preserve._.PreservesCCC-rf
d_PreservesCCC'45'rf_180 ::
  (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152) ->
  ()
d_PreservesCCC'45'rf_180 = erased
-- Once.Arith.Backend.X86-64.Preserve._.preserves-runFns
d_preserves'45'runFns_182 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  T_AgreeCCC_14
d_preserves'45'runFns_182 = erased
-- Once.Arith.Backend.X86-64.Preserve._.runFns
d_runFns_184 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152
d_runFns_184
  = coe MAlonzo.Code.Once.Arith.Backend.PreserveCore.du_runFns_52
-- Once.Arith.Backend.X86-64.Preserve._.step-of
d_step'45'of_186 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152
d_step'45'of_186
  = coe
      MAlonzo.Code.Once.Arith.Backend.PreserveCore.du_step'45'of_110
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_254)
      (coe MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Confine.d_writes_10)
-- Once.Arith.Backend.X86-64.Preserve._.step-of-preserves
d_step'45'of'45'preserves_188 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  T_AgreeCCC_14
d_step'45'of'45'preserves_188 = erased
-- Once.Arith.Backend.X86-64.Preserve._.write-regs
d_write'45'regs_190 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152
d_write'45'regs_190
  = coe
      MAlonzo.Code.Once.Arith.Backend.PreserveCore.du_write'45'regs_78
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_254)
-- Once.Arith.Backend.X86-64.Preserve._.write-regs-preserves
d_write'45'regs'45'preserves_192 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_RegFile_152 ->
  T_AgreeCCC_14
d_write'45'regs'45'preserves_192 = erased
