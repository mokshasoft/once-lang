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

module MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Target.RiscV64.Semantics.Word
d_Word_10 :: ()
d_Word_10 = erased
-- Once.CCC.Target.RiscV64.Semantics.offsetToℕ
d_offsetToℕ_12 :: Integer -> Integer
d_offsetToℕ_12 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe v0
      _ -> coe (0 :: Integer)
-- Once.CCC.Target.RiscV64.Semantics.isNegative
d_isNegative_18 :: Integer -> Bool
d_isNegative_18 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
-- Once.CCC.Target.RiscV64.Semantics.RegFile
d_RegFile_20 = ()
data T_RegFile_20
  = C_mkregfile_102 Integer Integer Integer Integer Integer Integer
                    Integer Integer Integer Integer Integer Integer Integer Integer
                    Integer Integer Integer Integer Integer Integer
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-ra
d_get'45'ra_62 :: T_RegFile_20 -> Integer
d_get'45'ra_62 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-sp
d_get'45'sp_64 :: T_RegFile_20 -> Integer
d_get'45'sp_64 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-fp
d_get'45'fp_66 :: T_RegFile_20 -> Integer
d_get'45'fp_66 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a0
d_get'45'a0_68 :: T_RegFile_20 -> Integer
d_get'45'a0_68 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a1
d_get'45'a1_70 :: T_RegFile_20 -> Integer
d_get'45'a1_70 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a2
d_get'45'a2_72 :: T_RegFile_20 -> Integer
d_get'45'a2_72 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a3
d_get'45'a3_74 :: T_RegFile_20 -> Integer
d_get'45'a3_74 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a4
d_get'45'a4_76 :: T_RegFile_20 -> Integer
d_get'45'a4_76 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a5
d_get'45'a5_78 :: T_RegFile_20 -> Integer
d_get'45'a5_78 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a6
d_get'45'a6_80 :: T_RegFile_20 -> Integer
d_get'45'a6_80 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-a7
d_get'45'a7_82 :: T_RegFile_20 -> Integer
d_get'45'a7_82 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s1
d_get'45's1_84 :: T_RegFile_20 -> Integer
d_get'45's1_84 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s2
d_get'45's2_86 :: T_RegFile_20 -> Integer
d_get'45's2_86 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s3
d_get'45's3_88 :: T_RegFile_20 -> Integer
d_get'45's3_88 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-s4
d_get'45's4_90 :: T_RegFile_20 -> Integer
d_get'45's4_90 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t0
d_get'45't0_92 :: T_RegFile_20 -> Integer
d_get'45't0_92 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t1
d_get'45't1_94 :: T_RegFile_20 -> Integer
d_get'45't1_94 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t2
d_get'45't2_96 :: T_RegFile_20 -> Integer
d_get'45't2_96 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t3
d_get'45't3_98 :: T_RegFile_20 -> Integer
d_get'45't3_98 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v19
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.RegFile.get-t4
d_get'45't4_100 :: T_RegFile_20 -> Integer
d_get'45't4_100 v0
  = case coe v0 of
      C_mkregfile_102 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
        -> coe v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.readReg
d_readReg_104 ::
  T_RegFile_20 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer
d_readReg_104 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12
        -> coe d_get'45'ra_62 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14
        -> coe d_get'45'sp_64 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16
        -> coe d_get'45'fp_66 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18
        -> coe d_get'45'a0_68 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a1_20
        -> coe d_get'45'a1_70 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a2_22
        -> coe d_get'45'a2_72 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a3_24
        -> coe d_get'45'a3_74 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a4_26
        -> coe d_get'45'a4_76 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a5_28
        -> coe d_get'45'a5_78 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a6_30
        -> coe d_get'45'a6_80 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a7_32
        -> coe d_get'45'a7_82 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34
        -> coe d_get'45's1_84 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36
        -> coe d_get'45's2_86 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38
        -> coe d_get'45's3_88 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40
        -> coe d_get'45's4_90 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42
        -> coe d_get'45't0_92 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44
        -> coe d_get'45't1_94 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46
        -> coe d_get'45't2_96 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t3_48
        -> coe d_get'45't3_98 (coe v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t4_50
        -> coe d_get'45't4_100 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.writeReg
d_writeReg_148 ::
  T_RegFile_20 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer -> T_RegFile_20
d_writeReg_148 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10
        -> coe (\ v2 -> v0)
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe v2) (coe d_get'45'sp_64 (coe v0))
                  (coe d_get'45'fp_66 (coe v0)) (coe d_get'45'a0_68 (coe v0))
                  (coe d_get'45'a1_70 (coe v0)) (coe d_get'45'a2_72 (coe v0))
                  (coe d_get'45'a3_74 (coe v0)) (coe d_get'45'a4_76 (coe v0))
                  (coe d_get'45'a5_78 (coe v0)) (coe d_get'45'a6_80 (coe v0))
                  (coe d_get'45'a7_82 (coe v0)) (coe d_get'45's1_84 (coe v0))
                  (coe d_get'45's2_86 (coe v0)) (coe d_get'45's3_88 (coe v0))
                  (coe d_get'45's4_90 (coe v0)) (coe d_get'45't0_92 (coe v0))
                  (coe d_get'45't1_94 (coe v0)) (coe d_get'45't2_96 (coe v0))
                  (coe d_get'45't3_98 (coe v0)) (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0)) (coe v2)
                  (coe d_get'45'fp_66 (coe v0)) (coe d_get'45'a0_68 (coe v0))
                  (coe d_get'45'a1_70 (coe v0)) (coe d_get'45'a2_72 (coe v0))
                  (coe d_get'45'a3_74 (coe v0)) (coe d_get'45'a4_76 (coe v0))
                  (coe d_get'45'a5_78 (coe v0)) (coe d_get'45'a6_80 (coe v0))
                  (coe d_get'45'a7_82 (coe v0)) (coe d_get'45's1_84 (coe v0))
                  (coe d_get'45's2_86 (coe v0)) (coe d_get'45's3_88 (coe v0))
                  (coe d_get'45's4_90 (coe v0)) (coe d_get'45't0_92 (coe v0))
                  (coe d_get'45't1_94 (coe v0)) (coe d_get'45't2_96 (coe v0))
                  (coe d_get'45't3_98 (coe v0)) (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe v2)
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe v2) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a1_20
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe v2)
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a2_22
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe v2) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a3_24
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe v2)
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a4_26
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe v2) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a5_28
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe v2)
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a6_30
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe v2) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a7_32
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe v2)
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe v2) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe v2)
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe v2) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe v2)
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe v2) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe v2)
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe v2) (coe d_get'45't3_98 (coe v0))
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t3_48
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe v2)
                  (coe d_get'45't4_100 (coe v0)))
      MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t4_50
        -> coe
             (\ v2 ->
                coe
                  C_mkregfile_102 (coe d_get'45'ra_62 (coe v0))
                  (coe d_get'45'sp_64 (coe v0)) (coe d_get'45'fp_66 (coe v0))
                  (coe d_get'45'a0_68 (coe v0)) (coe d_get'45'a1_70 (coe v0))
                  (coe d_get'45'a2_72 (coe v0)) (coe d_get'45'a3_74 (coe v0))
                  (coe d_get'45'a4_76 (coe v0)) (coe d_get'45'a5_78 (coe v0))
                  (coe d_get'45'a6_80 (coe v0)) (coe d_get'45'a7_82 (coe v0))
                  (coe d_get'45's1_84 (coe v0)) (coe d_get'45's2_86 (coe v0))
                  (coe d_get'45's3_88 (coe v0)) (coe d_get'45's4_90 (coe v0))
                  (coe d_get'45't0_92 (coe v0)) (coe d_get'45't1_94 (coe v0))
                  (coe d_get'45't2_96 (coe v0)) (coe d_get'45't3_98 (coe v0))
                  (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.Memory
d_Memory_234 :: ()
d_Memory_234 = erased
-- Once.CCC.Target.RiscV64.Semantics.readMem
d_readMem_236 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_236 v0 v1 = coe v0 v1
-- Once.CCC.Target.RiscV64.Semantics.writeMem
d_writeMem_242 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_242 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.CCC.Target.RiscV64.Semantics.State
d_State_252 = ()
data T_State_252
  = C_mkstate_270 T_RegFile_20 (Integer -> Maybe Integer) Integer
                  Bool
-- Once.CCC.Target.RiscV64.Semantics.State.regs
d_regs_262 :: T_State_252 -> T_RegFile_20
d_regs_262 v0
  = case coe v0 of
      C_mkstate_270 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.State.memory
d_memory_264 :: T_State_252 -> Integer -> Maybe Integer
d_memory_264 v0
  = case coe v0 of
      C_mkstate_270 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.State.pc
d_pc_266 :: T_State_252 -> Integer
d_pc_266 v0
  = case coe v0 of
      C_mkstate_270 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.State.halted
d_halted_268 :: T_State_252 -> Bool
d_halted_268 v0
  = case coe v0 of
      C_mkstate_270 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.emptyRegFile
d_emptyRegFile_272 :: T_RegFile_20
d_emptyRegFile_272
  = coe
      C_mkregfile_102 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.emptyMemory
d_emptyMemory_274 :: Integer -> Maybe Integer
d_emptyMemory_274 ~v0 = du_emptyMemory_274
du_emptyMemory_274 :: Maybe Integer
du_emptyMemory_274
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Target.RiscV64.Semantics.initState
d_initState_278 :: T_State_252
d_initState_278
  = coe
      C_mkstate_270 (coe d_emptyRegFile_272)
      (\ v0 -> coe du_emptyMemory_274) (coe (0 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.CCC.Target.RiscV64.Semantics.effectiveAddr
d_effectiveAddr_280 ::
  T_RegFile_20 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer -> Integer
d_effectiveAddr_280 v0 v1 v2
  = coe addInt (coe d_readReg_104 (coe v0) (coe v1)) (coe v2)
-- Once.CCC.Target.RiscV64.Semantics.effectiveAddrSigned
d_effectiveAddrSigned_288 ::
  T_RegFile_20 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 ->
  Integer -> Integer
d_effectiveAddrSigned_288 v0 v1 v2
  = let v3 = d_isNegative_18 (coe v2) in
    coe
      (if coe v3
         then coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                (d_readReg_104 (coe v0) (coe v1))
                (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2))
         else coe
                addInt (coe d_readReg_104 (coe v0) (coe v1))
                (coe d_offsetToℕ_12 (coe v2)))
-- Once.CCC.Target.RiscV64.Semantics.pcPlusOffset
d_pcPlusOffset_312 :: Integer -> Integer -> Integer
d_pcPlusOffset_312 v0 v1
  = let v2 = d_isNegative_18 (coe v1) in
    coe
      (if coe v2
         then coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0
                (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
         else coe addInt (coe d_offsetToℕ_12 (coe v1)) (coe v0))
-- Once.CCC.Target.RiscV64.Semantics.fetch
d_fetch_330 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10
d_fetch_330 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_fetch_330 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.find-label-go
d_find'45'label'45'go_338 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_6 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  Integer -> Maybe Integer
d_find'45'label'45'go_338 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v3 v4
        -> let v5
                 = d_find'45'label'45'go_338
                     (coe v0) (coe v4) (coe addInt (coe (1 :: Integer)) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7480'__14 (coe v6)
                          (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                       (coe
                          d_find'45'label'45'go_338 (coe v0) (coe v4)
                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.find-label
d_find'45'label_356 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_6 -> Maybe Integer
d_find'45'label_356 v0 v1
  = coe
      d_find'45'label'45'go_338 (coe v1) (coe v0) (coe (0 :: Integer))
-- Once.CCC.Target.RiscV64.Semantics.jump-to
d_jump'45'to_362 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_252 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_6 -> Maybe T_State_252
d_jump'45'to_362 v0 v1 v2
  = let v3
          = d_find'45'label'45'go_338
              (coe v2) (coe v0) (coe (0 :: Integer)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_270 (coe d_regs_262 (coe v1)) (coe d_memory_264 (coe v1))
                   (coe v4) (coe d_halted_268 (coe v1)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_270 (coe d_regs_262 (coe v1)) (coe d_memory_264 (coe v1))
                   (coe d_pc_266 (coe v1))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.RiscV64.Semantics.execInstr
d_execInstr_388 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_252 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10 ->
  Maybe T_State_252
d_execInstr_388 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12 v3 v4 v5
        -> let v6
                 = coe
                     d_memory_264 v1
                     (d_effectiveAddr_280
                        (coe d_regs_262 (coe v1)) (coe v4) (coe v5)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          C_mkstate_270 (coe d_writeReg_148 (d_regs_262 (coe v1)) v3 v7)
                          (coe d_memory_264 (coe v1))
                          (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                          (coe d_halted_268 (coe v1)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270 (coe d_regs_262 (coe v1))
                (coe
                   d_writeMem_242 (coe d_memory_264 (coe v1))
                   (coe
                      d_effectiveAddr_280 (coe d_regs_262 (coe v1)) (coe v4) (coe v5))
                   (coe d_readReg_104 (coe d_regs_262 (coe v1)) (coe v3)))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_add_16 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270
                (coe
                   d_writeReg_148 (d_regs_262 (coe v1)) v3
                   (addInt
                      (coe d_readReg_104 (coe d_regs_262 (coe v1)) (coe v4))
                      (coe d_readReg_104 (coe d_regs_262 (coe v1)) (coe v5))))
                (coe d_memory_264 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270
                (coe
                   d_writeReg_148 (d_regs_262 (coe v1)) v3
                   (coe
                      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                      (d_readReg_104 (coe d_regs_262 (coe v1)) (coe v4))
                      (d_readReg_104 (coe d_regs_262 (coe v1)) (coe v5))))
                (coe d_memory_264 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_20 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270
                (coe
                   d_writeReg_148 (d_regs_262 (coe v1)) v3
                   (coe
                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                      (coe d_isNegative_18 (coe v5))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                         (d_readReg_104 (coe d_regs_262 (coe v1)) (coe v4))
                         (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v5)))
                      (coe
                         addInt (coe d_readReg_104 (coe d_regs_262 (coe v1)) (coe v4))
                         (coe d_offsetToℕ_12 (coe v5)))))
                (coe d_memory_264 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_22 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270
                (coe
                   d_writeReg_148 (d_regs_262 (coe v1)) v3
                   (coe
                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                      (coe d_isNegative_18 (coe v4)) (coe (0 :: Integer))
                      (coe d_offsetToℕ_12 (coe v4))))
                (coe d_memory_264 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_auipc_24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270
                (coe
                   d_writeReg_148 (d_regs_262 (coe v1)) v3
                   (addInt
                      (coe d_pc_266 (coe v1))
                      (coe mulInt (coe v4) (coe (4096 :: Integer)))))
                (coe d_memory_264 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla_26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270
                (coe d_writeReg_148 (d_regs_262 (coe v1)) v3 (0 :: Integer))
                (coe d_memory_264 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_28 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270
                (coe
                   d_writeReg_148 (d_regs_262 (coe v1)) v3
                   (d_readReg_104 (coe d_regs_262 (coe v1)) (coe v4)))
                (coe d_memory_264 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_30 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                eqInt (coe d_readReg_104 (coe d_regs_262 (coe v1)) (coe v3))
                (coe d_readReg_104 (coe d_regs_262 (coe v1)) (coe v4)))
             (coe d_jump'45'to_362 (coe v0) (coe v1) (coe v5))
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_270 (coe d_regs_262 (coe v1)) (coe d_memory_264 (coe v1))
                   (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                   (coe d_halted_268 (coe v1))))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bne_32 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                eqInt (coe d_readReg_104 (coe d_regs_262 (coe v1)) (coe v3))
                (coe d_readReg_104 (coe d_regs_262 (coe v1)) (coe v4)))
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   C_mkstate_270 (coe d_regs_262 (coe v1)) (coe d_memory_264 (coe v1))
                   (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                   (coe d_halted_268 (coe v1))))
             (coe d_jump'45'to_362 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jal_34 v3 v4
        -> coe
             d_jump'45'to_362 (coe v0)
             (coe
                C_mkstate_270
                (coe
                   d_writeReg_148 (d_regs_262 (coe v1)) v3
                   (addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1))))
                (coe d_memory_264 (coe v1)) (coe d_pc_266 (coe v1))
                (coe d_halted_268 (coe v1)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_36 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270
                (coe
                   d_writeReg_148 (d_regs_262 (coe v1)) v3
                   (addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1))))
                (coe d_memory_264 (coe v1))
                (coe
                   d_effectiveAddr_280 (coe d_regs_262 (coe v1)) (coe v4) (coe v5))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_38 v3
        -> coe d_jump'45'to_362 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ret_40
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270 (coe d_regs_262 (coe v1)) (coe d_memory_264 (coe v1))
                (coe
                   d_readReg_104 (coe d_regs_262 (coe v1))
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call_42 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270
                (coe
                   d_writeReg_148 (d_regs_262 (coe v1))
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                   (addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1))))
                (coe d_memory_264 (coe v1))
                (coe addInt (coe d_pc_266 (coe v1)) (coe v3))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_44 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270 (coe d_regs_262 (coe v1)) (coe d_memory_264 (coe v1))
                (coe d_pc_266 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_nop_46
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270 (coe d_regs_262 (coe v1)) (coe d_memory_264 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                (coe d_halted_268 (coe v1)))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_unimp_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270 (coe d_regs_262 (coe v1)) (coe d_memory_264 (coe v1))
                (coe d_pc_266 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_50 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_mkstate_270 (coe d_regs_262 (coe v1)) (coe d_memory_264 (coe v1))
                (coe addInt (coe (1 :: Integer)) (coe d_pc_266 (coe v1)))
                (coe d_halted_268 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.Semantics.step
d_step_606 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_252 -> Maybe T_State_252
d_step_606 v0 v1
  = let v2 = d_halted_268 (coe v1) in
    coe
      (if coe v2
         then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
         else (let v3 = d_fetch_330 (coe v0) (coe d_pc_266 (coe v1)) in
               coe
                 (case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                      -> coe d_execInstr_388 (coe v0) (coe v1) (coe v4)
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              C_mkstate_270 (coe d_regs_262 (coe v1)) (coe d_memory_264 (coe v1))
                              (coe d_pc_266 (coe v1))
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.CCC.Target.RiscV64.Semantics.exec
d_exec_638 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_252 -> Maybe T_State_252
d_exec_638 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v4 = d_halted_268 (coe v2) in
              coe
                (if coe v4
                   then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                   else (let v5 = d_fetch_330 (coe v1) (coe d_pc_266 (coe v2)) in
                         coe
                           (case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                -> let v7 = d_execInstr_388 (coe v1) (coe v2) (coe v6) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> let v9 = d_halted_268 (coe v8) in
                                             coe
                                               (if coe v9
                                                  then coe v7
                                                  else coe d_exec_638 (coe v3) (coe v1) (coe v8))
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> let v6
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                             (coe
                                                C_mkstate_270 (coe d_regs_262 (coe v2))
                                                (coe d_memory_264 (coe v2)) (coe d_pc_266 (coe v2))
                                                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)) in
                                   coe
                                     (let v7
                                            = coe
                                                C_mkstate_270 (coe d_regs_262 (coe v2))
                                                (coe d_memory_264 (coe v2)) (coe d_pc_266 (coe v2))
                                                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) in
                                      coe
                                        (let v8 = d_halted_268 (coe v7) in
                                         coe
                                           (if coe v8
                                              then coe v6
                                              else coe d_exec_638 (coe v3) (coe v1) (coe v7))))
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Target.RiscV64.Semantics.exec-until-pc
d_exec'45'until'45'pc_690 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_252 -> Maybe T_State_252
d_exec'45'until'45'pc_690 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v5 = d_halted_268 (coe v3) in
              coe
                (if coe v5
                   then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                   else (let v6
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v6 ->
                                      coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                        (coe d_pc_266 (coe v3)))
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                      (coe eqInt (coe d_pc_266 (coe v3)) (coe v0))) in
                         coe
                           (case coe v6 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                -> if coe v7
                                     then coe
                                            seq (coe v8)
                                            (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3))
                                     else coe
                                            seq (coe v8)
                                            (let v9
                                                   = d_fetch_330 (coe v2) (coe d_pc_266 (coe v3)) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = d_execInstr_388
                                                                 (coe v2) (coe v3) (coe v10) in
                                                       coe
                                                         (case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                              -> coe
                                                                   d_exec'45'until'45'pc_690
                                                                   (coe v0) (coe v4) (coe v2)
                                                                   (coe v12)
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe v11
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 C_mkstate_270
                                                                 (coe d_regs_262 (coe v3))
                                                                 (coe d_memory_264 (coe v3))
                                                                 (coe d_pc_266 (coe v3))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Bool.C_true_10) in
                                                       coe
                                                         (coe
                                                            d_exec'45'until'45'pc_690 (coe v0)
                                                            (coe v4) (coe v2) (coe v10))
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Target.RiscV64.Semantics.defaultFuel
d_defaultFuel_768 :: Integer
d_defaultFuel_768 = coe (10000 :: Integer)
-- Once.CCC.Target.RiscV64.Semantics.run
d_run_770 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  T_State_252 -> Maybe T_State_252
d_run_770 = coe d_exec_638 (coe d_defaultFuel_768)
