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

module MAlonzo.Code.Once.Arith.Backend.RiscV64.Preserve where

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
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.Confine
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg

-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC
d_AgreeCCC_14 a0 a1 = ()
data T_AgreeCCC_14 = C_mkAgree_84
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-zero
d_a'45'zero_52 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'zero_52 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-ra
d_a'45'ra_54 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'ra_54 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-sp
d_a'45'sp_56 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'sp_56 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-fp
d_a'45'fp_58 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'fp_58 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-a1
d_a'45'a1_60 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'a1_60 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-a2
d_a'45'a2_62 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'a2_62 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-a6
d_a'45'a6_64 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'a6_64 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-a7
d_a'45'a7_66 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45'a7_66 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-s1
d_a'45's1_68 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45's1_68 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-s2
d_a'45's2_70 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45's2_70 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-s3
d_a'45's3_72 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45's3_72 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-s4
d_a'45's4_74 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45's4_74 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-t1
d_a'45't1_76 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45't1_76 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-t2
d_a'45't2_78 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45't2_78 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-t3
d_a'45't3_80 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45't3_80 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC.a-t4
d_a'45't4_82 ::
  T_AgreeCCC_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'45't4_82 = erased
-- Once.Arith.Backend.RiscV64.Preserve.agree-refl-ccc
d_agree'45'refl'45'ccc_88 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  T_AgreeCCC_14
d_agree'45'refl'45'ccc_88 = erased
-- Once.Arith.Backend.RiscV64.Preserve.write-nonccc-agrees
d_write'45'nonccc'45'agrees_98 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_AgreeCCC_14
d_write'45'nonccc'45'agrees_98 = erased
-- Once.Arith.Backend.RiscV64.Preserve.AgreeCCC-trans
d_AgreeCCC'45'trans_222 ::
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  T_AgreeCCC_14 -> T_AgreeCCC_14 -> T_AgreeCCC_14
d_AgreeCCC'45'trans_222 = erased
-- Once.Arith.Backend.RiscV64.Preserve._.PreservesCCC-rf
d_PreservesCCC'45'rf_290 ::
  (MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174) ->
  ()
d_PreservesCCC'45'rf_290 = erased
-- Once.Arith.Backend.RiscV64.Preserve._.preserves-runFns
d_preserves'45'runFns_292 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  T_AgreeCCC_14
d_preserves'45'runFns_292 = erased
-- Once.Arith.Backend.RiscV64.Preserve._.runFns
d_runFns_294 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174
d_runFns_294
  = coe MAlonzo.Code.Once.Arith.Backend.PreserveCore.du_runFns_52
-- Once.Arith.Backend.RiscV64.Preserve._.step-of
d_step'45'of_296 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  (MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174
d_step'45'of_296
  = coe
      MAlonzo.Code.Once.Arith.Backend.PreserveCore.du_step'45'of_110
      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_writeReg_302)
      (coe MAlonzo.Code.Once.Arith.Backend.RiscV64.Confine.d_writes_10)
-- Once.Arith.Backend.RiscV64.Preserve._.step-of-preserves
d_step'45'of'45'preserves_298 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  (MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  T_AgreeCCC_14
d_step'45'of'45'preserves_298 = erased
-- Once.Arith.Backend.RiscV64.Preserve._.write-regs
d_write'45'regs_300 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174
d_write'45'regs_300
  = coe
      MAlonzo.Code.Once.Arith.Backend.PreserveCore.du_write'45'regs_78
      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_writeReg_302)
-- Once.Arith.Backend.RiscV64.Preserve._.write-regs-preserves
d_write'45'regs'45'preserves_302 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_RegFile_174 ->
  T_AgreeCCC_14
d_write'45'regs'45'preserves_302 = erased
