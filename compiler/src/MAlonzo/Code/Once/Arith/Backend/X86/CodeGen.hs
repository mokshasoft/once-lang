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

module MAlonzo.Code.Once.Arith.Backend.X86.CodeGen where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Arith.Backend.X86.Syntax
import qualified MAlonzo.Code.Once.Arith.IR
import qualified MAlonzo.Code.Once.Arith.Type

-- Once.Arith.Backend.X86.CodeGen.availableGPRs
d_availableGPRs_10 ::
  [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_GPReg_10]
d_availableGPRs_10
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r8_24)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r9_26)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r10_28)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r11_30)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rbx_14)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.Arith.Backend.X86.CodeGen.availableXMMs
d_availableXMMs_12 ::
  [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_XMMReg_90]
d_availableXMMs_12
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm1_94)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm2_96)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm3_98)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm4_100)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm5_102)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm6_104)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm7_106)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
-- Once.Arith.Backend.X86.CodeGen.AllocState
d_AllocState_14 = ()
data T_AllocState_14 = C_mkState_24 Integer Integer
-- Once.Arith.Backend.X86.CodeGen.AllocState.nextGPR
d_nextGPR_20 :: T_AllocState_14 -> Integer
d_nextGPR_20 v0
  = case coe v0 of
      C_mkState_24 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.AllocState.nextXMM
d_nextXMM_22 :: T_AllocState_14 -> Integer
d_nextXMM_22 v0
  = case coe v0 of
      C_mkState_24 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.initAlloc
d_initAlloc_26 :: T_AllocState_14
d_initAlloc_26
  = coe C_mkState_24 (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Arith.Backend.X86.CodeGen.getGPR
d_getGPR_28 ::
  Integer -> MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_GPReg_10
d_getGPR_28 v0
  = let v1
          = coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r8_24 in
    coe
      (case coe v0 of
         0 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r8_24
         1 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r9_26
         2 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r10_28
         3 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_r11_30
         4 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rbx_14
         _ -> coe v1)
-- Once.Arith.Backend.X86.CodeGen.getXMM
d_getXMM_30 ::
  Integer -> MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_XMMReg_90
d_getXMM_30 v0
  = let v1
          = coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm1_94 in
    coe
      (case coe v0 of
         0 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm1_94
         1 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm2_96
         2 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm3_98
         3 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm4_100
         4 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm5_102
         5 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm6_104
         6 -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm7_106
         _ -> coe v1)
-- Once.Arith.Backend.X86.CodeGen.allocGPR
d_allocGPR_32 ::
  T_AllocState_14 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_allocGPR_32 v0
  = case coe v0 of
      C_mkState_24 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_getGPR_28 (coe v1))
             (coe
                C_mkState_24 (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.allocXMM
d_allocXMM_38 ::
  T_AllocState_14 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_allocXMM_38 v0
  = case coe v0 of
      C_mkState_24 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe d_getXMM_30 (coe v2))
             (coe
                C_mkState_24 (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.freeGPR
d_freeGPR_44 :: T_AllocState_14 -> T_AllocState_14
d_freeGPR_44 v0
  = case coe v0 of
      C_mkState_24 v1 v2
        -> coe
             C_mkState_24
             (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 (1 :: Integer))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.freeXMM
d_freeXMM_50 :: T_AllocState_14 -> T_AllocState_14
d_freeXMM_50 v0
  = case coe v0 of
      C_mkState_24 v1 v2
        -> coe
             C_mkState_24 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2 (1 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.IntResult
d_IntResult_56 = ()
data T_IntResult_56
  = C_mkIntResult_70 [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithInstr_220]
                     MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_GPReg_10
                     T_AllocState_14
-- Once.Arith.Backend.X86.CodeGen.IntResult.code
d_code_64 ::
  T_IntResult_56 ->
  [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithInstr_220]
d_code_64 v0
  = case coe v0 of
      C_mkIntResult_70 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.IntResult.result
d_result_66 ::
  T_IntResult_56 ->
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_GPReg_10
d_result_66 v0
  = case coe v0 of
      C_mkIntResult_70 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.IntResult.state
d_state_68 :: T_IntResult_56 -> T_AllocState_14
d_state_68 v0
  = case coe v0 of
      C_mkIntResult_70 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.FloatResult
d_FloatResult_72 = ()
data T_FloatResult_72
  = C_mkFloatResult_86 [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithInstr_220]
                       MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_XMMReg_90
                       T_AllocState_14
-- Once.Arith.Backend.X86.CodeGen.FloatResult.code
d_code_80 ::
  T_FloatResult_72 ->
  [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithInstr_220]
d_code_80 v0
  = case coe v0 of
      C_mkFloatResult_86 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.FloatResult.result
d_result_82 ::
  T_FloatResult_72 ->
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_XMMReg_90
d_result_82 v0
  = case coe v0 of
      C_mkFloatResult_86 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.FloatResult.state
d_state_84 :: T_FloatResult_72 -> T_AllocState_14
d_state_84 v0
  = case coe v0 of
      C_mkFloatResult_86 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.toℤ
d_toℤ_90 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer
d_toℤ_90 v0 ~v1 v2 = du_toℤ_90 v0 v2
du_toℤ_90 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 -> AgdaAny -> Integer
du_toℤ_90 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.Arith.Backend.X86.CodeGen.cmpOpToCondCode
d_cmpOpToCondCode_100 ::
  MAlonzo.Code.Once.Arith.IR.T_CmpOp_58 ->
  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_CondCode_150
d_cmpOpToCondCode_100 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.IR.C_CmpLt_60
        -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'l_156
      MAlonzo.Code.Once.Arith.IR.C_CmpLe_62
        -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'le_158
      MAlonzo.Code.Once.Arith.IR.C_CmpGt_64
        -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'g_160
      MAlonzo.Code.Once.Arith.IR.C_CmpGe_66
        -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'ge_162
      MAlonzo.Code.Once.Arith.IR.C_CmpEq_68
        -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'e_152
      MAlonzo.Code.Once.Arith.IR.C_CmpNe_70
        -> coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cc'45'ne_154
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.compile-int
d_compile'45'int_106 ::
  [MAlonzo.Code.Once.Arith.IR.T_Binding_6] ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.IR.T_ArithIR_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AllocState_14 -> T_IntResult_56
d_compile'45'int_106 ~v0 v1 v2 ~v3 v4
  = du_compile'45'int_106 v1 v2 v4
du_compile'45'int_106 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.IR.T_ArithIR_72 ->
  T_AllocState_14 -> T_IntResult_56
du_compile'45'int_106 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Arith.IR.C_Lit_76 v4
        -> coe
             C_mkIntResult_70
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                   (coe
                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe d_allocGPR_32 (coe v2)))
                      (coe
                         MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_immI_142
                         (coe du_toℤ_90 (coe v0) (coe v4)))))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe d_allocGPR_32 (coe v2)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_allocGPR_32 (coe v2)))
      MAlonzo.Code.Once.Arith.IR.C_Var_84 v3 v6
        -> coe
             C_mkIntResult_70
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                   (coe
                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe d_allocGPR_32 (coe v2)))
                      (coe
                         MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_memI_140
                         (coe
                            MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_base_132
                            (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rdi_22)))))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe d_allocGPR_32 (coe v2)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_allocGPR_32 (coe v2)))
      MAlonzo.Code.Once.Arith.IR.C_Add_92 v3 v4 v6 v7
        -> coe
             C_mkIntResult_70
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_code_64 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      d_code_64
                      (coe
                         du_compile'45'int_106 (coe v0) (coe v7)
                         (coe
                            d_state_68
                            (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                         (coe
                            MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_addI_168
                            (coe
                               d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
                            (coe
                               MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138
                               (coe
                                  d_result_66
                                  (coe
                                     du_compile'45'int_106 (coe v0) (coe v7)
                                     (coe
                                        d_state_68
                                        (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2))))))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
             (coe
                d_freeGPR_44
                (coe
                   d_state_68
                   (coe
                      du_compile'45'int_106 (coe v0) (coe v7)
                      (coe
                         d_state_68
                         (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2))))))
      MAlonzo.Code.Once.Arith.IR.C_Sub_100 v3 v4 v6 v7
        -> coe
             C_mkIntResult_70
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_code_64 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      d_code_64
                      (coe
                         du_compile'45'int_106 (coe v0) (coe v7)
                         (coe
                            d_state_68
                            (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                         (coe
                            MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_subI_170
                            (coe
                               d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
                            (coe
                               MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138
                               (coe
                                  d_result_66
                                  (coe
                                     du_compile'45'int_106 (coe v0) (coe v7)
                                     (coe
                                        d_state_68
                                        (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2))))))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
             (coe
                d_freeGPR_44
                (coe
                   d_state_68
                   (coe
                      du_compile'45'int_106 (coe v0) (coe v7)
                      (coe
                         d_state_68
                         (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2))))))
      MAlonzo.Code.Once.Arith.IR.C_Mul_108 v3 v4 v6 v7
        -> coe
             C_mkIntResult_70
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_code_64 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      d_code_64
                      (coe
                         du_compile'45'int_106 (coe v0) (coe v7)
                         (coe
                            d_state_68
                            (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                         (coe
                            MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_imulI_172
                            (coe
                               d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
                            (coe
                               MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138
                               (coe
                                  d_result_66
                                  (coe
                                     du_compile'45'int_106 (coe v0) (coe v7)
                                     (coe
                                        d_state_68
                                        (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2))))))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
             (coe
                d_freeGPR_44
                (coe
                   d_state_68
                   (coe
                      du_compile'45'int_106 (coe v0) (coe v7)
                      (coe
                         d_state_68
                         (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2))))))
      MAlonzo.Code.Once.Arith.IR.C_Div_116 v3 v4 v6 v7
        -> coe
             C_mkIntResult_70
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_code_64 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      d_code_64
                      (coe
                         du_compile'45'int_106 (coe v0) (coe v7)
                         (coe
                            d_state_68
                            (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                         (coe
                            MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                            (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rax_12)
                            (coe
                               MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138
                               (coe
                                  d_result_66
                                  (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2))))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                            (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cqo_176))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                               (coe
                                  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_idivI_178
                                  (coe
                                     MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138
                                     (coe
                                        d_result_66
                                        (coe
                                           du_compile'45'int_106 (coe v0) (coe v7)
                                           (coe
                                              d_state_68
                                              (coe
                                                 du_compile'45'int_106 (coe v0) (coe v6)
                                                 (coe v2))))))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                                  (coe
                                     MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                                     (coe
                                        d_result_66
                                        (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
                                     (coe
                                        MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138
                                        (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rax_12))))
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
             (coe
                d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
             (coe
                d_freeGPR_44
                (coe
                   d_state_68
                   (coe
                      du_compile'45'int_106 (coe v0) (coe v7)
                      (coe
                         d_state_68
                         (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2))))))
      MAlonzo.Code.Once.Arith.IR.C_Mod_124 v3 v4 v6 v7
        -> coe
             C_mkIntResult_70
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_code_64 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      d_code_64
                      (coe
                         du_compile'45'int_106 (coe v0) (coe v7)
                         (coe
                            d_state_68
                            (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                         (coe
                            MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                            (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rax_12)
                            (coe
                               MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138
                               (coe
                                  d_result_66
                                  (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2))))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                            (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cqo_176))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                               (coe
                                  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_idivI_178
                                  (coe
                                     MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138
                                     (coe
                                        d_result_66
                                        (coe
                                           du_compile'45'int_106 (coe v0) (coe v7)
                                           (coe
                                              d_state_68
                                              (coe
                                                 du_compile'45'int_106 (coe v0) (coe v6)
                                                 (coe v2))))))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                                  (coe
                                     MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                                     (coe
                                        d_result_66
                                        (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
                                     (coe
                                        MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138
                                        (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rdx_18))))
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
             (coe
                d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2)))
             (coe
                d_freeGPR_44
                (coe
                   d_state_68
                   (coe
                      du_compile'45'int_106 (coe v0) (coe v7)
                      (coe
                         d_state_68
                         (coe du_compile'45'int_106 (coe v0) (coe v6) (coe v2))))))
      MAlonzo.Code.Once.Arith.IR.C_Neg_130 v5
        -> coe
             C_mkIntResult_70
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_code_64 (coe du_compile'45'int_106 (coe v0) (coe v5) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                      (coe
                         MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_negI_174
                         (coe
                            d_result_66
                            (coe du_compile'45'int_106 (coe v0) (coe v5) (coe v2)))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe
                d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v5) (coe v2)))
             (coe
                d_state_68 (coe du_compile'45'int_106 (coe v0) (coe v5) (coe v2)))
      MAlonzo.Code.Once.Arith.IR.C_Cmp_138 v3 v4 v6 v7 v8
        -> coe
             C_mkIntResult_70
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_code_64 (coe du_compile'45'int_106 (coe v0) (coe v7) (coe v2)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      d_code_64
                      (coe
                         du_compile'45'int_106 (coe v0) (coe v8)
                         (coe
                            d_state_68
                            (coe du_compile'45'int_106 (coe v0) (coe v7) (coe v2)))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                         (coe
                            MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cmpI_184
                            (coe
                               d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v7) (coe v2)))
                            (coe
                               MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138
                               (coe
                                  d_result_66
                                  (coe
                                     du_compile'45'int_106 (coe v0) (coe v8)
                                     (coe
                                        d_state_68
                                        (coe du_compile'45'int_106 (coe v0) (coe v7) (coe v2))))))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                            (coe
                               MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_setccI_186
                               (coe d_cmpOpToCondCode_100 (coe v6))
                               (coe
                                  d_result_66
                                  (coe du_compile'45'int_106 (coe v0) (coe v7) (coe v2)))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                               (coe
                                  MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movzxI_188
                                  (coe
                                     d_result_66
                                     (coe du_compile'45'int_106 (coe v0) (coe v7) (coe v2)))
                                  (coe
                                     d_result_66
                                     (coe du_compile'45'int_106 (coe v0) (coe v7) (coe v2)))))
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
             (coe
                d_result_66 (coe du_compile'45'int_106 (coe v0) (coe v7) (coe v2)))
             (coe
                d_freeGPR_44
                (coe
                   d_state_68
                   (coe
                      du_compile'45'int_106 (coe v0) (coe v8)
                      (coe
                         d_state_68
                         (coe du_compile'45'int_106 (coe v0) (coe v7) (coe v2))))))
      MAlonzo.Code.Once.Arith.IR.C_Conv_146 v4 v6
        -> coe
             seq (coe v0)
             (case coe v4 of
                MAlonzo.Code.Once.Arith.Type.C_I8_8
                  -> coe du_compile'45'int_106 (coe v4) (coe v6) (coe v2)
                MAlonzo.Code.Once.Arith.Type.C_I16_10
                  -> coe du_compile'45'int_106 (coe v4) (coe v6) (coe v2)
                MAlonzo.Code.Once.Arith.Type.C_I32_12
                  -> coe du_compile'45'int_106 (coe v4) (coe v6) (coe v2)
                MAlonzo.Code.Once.Arith.Type.C_I64_14
                  -> coe du_compile'45'int_106 (coe v4) (coe v6) (coe v2)
                MAlonzo.Code.Once.Arith.Type.C_F32_16
                  -> coe
                       C_mkIntResult_70
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe d_allocGPR_32 (coe v2)))
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_immI_142
                                   (coe (0 :: Integer)))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_allocGPR_32 (coe v2)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_allocGPR_32 (coe v2)))
                MAlonzo.Code.Once.Arith.Type.C_F64_18
                  -> coe
                       C_mkIntResult_70
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe d_allocGPR_32 (coe v2)))
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_immI_142
                                   (coe (0 :: Integer)))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_allocGPR_32 (coe v2)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_allocGPR_32 (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.compile-float
d_compile'45'float_454 ::
  [MAlonzo.Code.Once.Arith.IR.T_Binding_6] ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.IR.T_ArithIR_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_AllocState_14 -> T_FloatResult_72
d_compile'45'float_454 ~v0 v1 v2 ~v3 v4
  = du_compile'45'float_454 v1 v2 v4
du_compile'45'float_454 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.IR.T_ArithIR_72 ->
  T_AllocState_14 -> T_FloatResult_72
du_compile'45'float_454 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Type.C_F32_16
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.IR.C_Lit_76 v4
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movss_192
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe d_allocXMM_38 (coe v2)))
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_memF_148
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_base_132
                                   (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rdi_22)))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe d_allocXMM_38 (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe d_allocXMM_38 (coe v2)))
             MAlonzo.Code.Once.Arith.IR.C_Var_84 v3 v6
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movss_192
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe d_allocXMM_38 (coe v2)))
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_memF_148
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_base_132
                                   (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rdi_22)))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe d_allocXMM_38 (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe d_allocXMM_38 (coe v2)))
             MAlonzo.Code.Once.Arith.IR.C_Add_92 v3 v4 v6 v7
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_code_80
                             (coe
                                du_compile'45'float_454 (coe v0) (coe v7)
                                (coe
                                   d_state_84
                                   (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_addss_196
                                   (coe
                                      d_result_82
                                      (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146
                                      (coe
                                         d_result_82
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v7)
                                            (coe
                                               d_state_84
                                               (coe
                                                  du_compile'45'float_454 (coe v0) (coe v6)
                                                  (coe v2))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_state_84
                          (coe
                             du_compile'45'float_454 (coe v0) (coe v7)
                             (coe
                                d_state_84
                                (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2))))))
             MAlonzo.Code.Once.Arith.IR.C_Sub_100 v3 v4 v6 v7
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_code_80
                             (coe
                                du_compile'45'float_454 (coe v0) (coe v7)
                                (coe
                                   d_state_84
                                   (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_subss_198
                                   (coe
                                      d_result_82
                                      (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146
                                      (coe
                                         d_result_82
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v7)
                                            (coe
                                               d_state_84
                                               (coe
                                                  du_compile'45'float_454 (coe v0) (coe v6)
                                                  (coe v2))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_state_84
                          (coe
                             du_compile'45'float_454 (coe v0) (coe v7)
                             (coe
                                d_state_84
                                (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2))))))
             MAlonzo.Code.Once.Arith.IR.C_Mul_108 v3 v4 v6 v7
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_code_80
                             (coe
                                du_compile'45'float_454 (coe v0) (coe v7)
                                (coe
                                   d_state_84
                                   (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_mulss_200
                                   (coe
                                      d_result_82
                                      (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146
                                      (coe
                                         d_result_82
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v7)
                                            (coe
                                               d_state_84
                                               (coe
                                                  du_compile'45'float_454 (coe v0) (coe v6)
                                                  (coe v2))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_state_84
                          (coe
                             du_compile'45'float_454 (coe v0) (coe v7)
                             (coe
                                d_state_84
                                (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2))))))
             MAlonzo.Code.Once.Arith.IR.C_Div_116 v3 v4 v6 v7
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_code_80
                             (coe
                                du_compile'45'float_454 (coe v0) (coe v7)
                                (coe
                                   d_state_84
                                   (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_divss_202
                                   (coe
                                      d_result_82
                                      (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146
                                      (coe
                                         d_result_82
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v7)
                                            (coe
                                               d_state_84
                                               (coe
                                                  du_compile'45'float_454 (coe v0) (coe v6)
                                                  (coe v2))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_state_84
                          (coe
                             du_compile'45'float_454 (coe v0) (coe v7)
                             (coe
                                d_state_84
                                (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2))))))
             MAlonzo.Code.Once.Arith.IR.C_Mod_124 v3 v4 v6 v7
               -> coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)
             MAlonzo.Code.Once.Arith.IR.C_Neg_130 v5
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v5) (coe v2)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_allocGPR_32
                                      (coe
                                         d_state_84
                                         (coe du_compile'45'float_454 (coe v0) (coe v5) (coe v2)))))
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_immI_142
                                   (coe (2147483648 :: Integer)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movqToXMM_216
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_allocXMM_38
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_allocGPR_32
                                               (coe
                                                  d_state_84
                                                  (coe
                                                     du_compile'45'float_454 (coe v0) (coe v5)
                                                     (coe v2)))))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_allocGPR_32
                                         (coe
                                            d_state_84
                                            (coe
                                               du_compile'45'float_454 (coe v0) (coe v5)
                                               (coe v2)))))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorps_212
                                      (coe
                                         d_result_82
                                         (coe du_compile'45'float_454 (coe v0) (coe v5) (coe v2)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_allocXMM_38
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_allocGPR_32
                                                  (coe
                                                     d_state_84
                                                     (coe
                                                        du_compile'45'float_454 (coe v0) (coe v5)
                                                        (coe v2)))))))))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v5) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_freeGPR_44
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_allocXMM_38
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_allocGPR_32
                                      (coe
                                         d_state_84
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v5)
                                            (coe v2)))))))))
             MAlonzo.Code.Once.Arith.IR.C_Cmp_138 v3 v4 v6 v7 v8
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v7) (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_code_80
                             (coe
                                du_compile'45'float_454 (coe v0) (coe v8)
                                (coe
                                   d_state_84
                                   (coe du_compile'45'float_454 (coe v0) (coe v7) (coe v2)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_subss_198
                                   (coe
                                      d_result_82
                                      (coe du_compile'45'float_454 (coe v0) (coe v7) (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146
                                      (coe
                                         d_result_82
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v8)
                                            (coe
                                               d_state_84
                                               (coe
                                                  du_compile'45'float_454 (coe v0) (coe v7)
                                                  (coe v2))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v7) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_state_84
                          (coe
                             du_compile'45'float_454 (coe v0) (coe v8)
                             (coe
                                d_state_84
                                (coe du_compile'45'float_454 (coe v0) (coe v7) (coe v2))))))
             MAlonzo.Code.Once.Arith.IR.C_Conv_146 v4 v6
               -> case coe v4 of
                    MAlonzo.Code.Once.Arith.Type.C_I8_8
                      -> coe
                           C_mkFloatResult_86
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorps_212
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe d_allocXMM_38 (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_allocXMM_38 (coe v2)))
                    MAlonzo.Code.Once.Arith.Type.C_I16_10
                      -> coe
                           C_mkFloatResult_86
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorps_212
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe d_allocXMM_38 (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_allocXMM_38 (coe v2)))
                    MAlonzo.Code.Once.Arith.Type.C_I32_12
                      -> coe
                           C_mkFloatResult_86
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorps_212
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe d_allocXMM_38 (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_allocXMM_38 (coe v2)))
                    MAlonzo.Code.Once.Arith.Type.C_I64_14
                      -> coe
                           C_mkFloatResult_86
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorps_212
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe d_allocXMM_38 (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_allocXMM_38 (coe v2)))
                    MAlonzo.Code.Once.Arith.Type.C_F32_16
                      -> coe du_compile'45'float_454 (coe v4) (coe v6) (coe v2)
                    MAlonzo.Code.Once.Arith.Type.C_F64_18
                      -> coe du_compile'45'float_454 (coe v4) (coe v6) (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Type.C_F64_18
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.IR.C_Lit_76 v4
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movsd_194
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe d_allocXMM_38 (coe v2)))
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_memF_148
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_base_132
                                   (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rdi_22)))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe d_allocXMM_38 (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe d_allocXMM_38 (coe v2)))
             MAlonzo.Code.Once.Arith.IR.C_Var_84 v3 v6
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movsd_194
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe d_allocXMM_38 (coe v2)))
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_memF_148
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_base_132
                                   (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rdi_22)))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe d_allocXMM_38 (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe d_allocXMM_38 (coe v2)))
             MAlonzo.Code.Once.Arith.IR.C_Add_92 v3 v4 v6 v7
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_code_80
                             (coe
                                du_compile'45'float_454 (coe v0) (coe v7)
                                (coe
                                   d_state_84
                                   (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_addsd_204
                                   (coe
                                      d_result_82
                                      (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146
                                      (coe
                                         d_result_82
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v7)
                                            (coe
                                               d_state_84
                                               (coe
                                                  du_compile'45'float_454 (coe v0) (coe v6)
                                                  (coe v2))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_state_84
                          (coe
                             du_compile'45'float_454 (coe v0) (coe v7)
                             (coe
                                d_state_84
                                (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2))))))
             MAlonzo.Code.Once.Arith.IR.C_Sub_100 v3 v4 v6 v7
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_code_80
                             (coe
                                du_compile'45'float_454 (coe v0) (coe v7)
                                (coe
                                   d_state_84
                                   (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_subsd_206
                                   (coe
                                      d_result_82
                                      (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146
                                      (coe
                                         d_result_82
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v7)
                                            (coe
                                               d_state_84
                                               (coe
                                                  du_compile'45'float_454 (coe v0) (coe v6)
                                                  (coe v2))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_state_84
                          (coe
                             du_compile'45'float_454 (coe v0) (coe v7)
                             (coe
                                d_state_84
                                (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2))))))
             MAlonzo.Code.Once.Arith.IR.C_Mul_108 v3 v4 v6 v7
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_code_80
                             (coe
                                du_compile'45'float_454 (coe v0) (coe v7)
                                (coe
                                   d_state_84
                                   (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_mulsd_208
                                   (coe
                                      d_result_82
                                      (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146
                                      (coe
                                         d_result_82
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v7)
                                            (coe
                                               d_state_84
                                               (coe
                                                  du_compile'45'float_454 (coe v0) (coe v6)
                                                  (coe v2))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_state_84
                          (coe
                             du_compile'45'float_454 (coe v0) (coe v7)
                             (coe
                                d_state_84
                                (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2))))))
             MAlonzo.Code.Once.Arith.IR.C_Div_116 v3 v4 v6 v7
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_code_80
                             (coe
                                du_compile'45'float_454 (coe v0) (coe v7)
                                (coe
                                   d_state_84
                                   (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_divsd_210
                                   (coe
                                      d_result_82
                                      (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146
                                      (coe
                                         d_result_82
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v7)
                                            (coe
                                               d_state_84
                                               (coe
                                                  du_compile'45'float_454 (coe v0) (coe v6)
                                                  (coe v2))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_state_84
                          (coe
                             du_compile'45'float_454 (coe v0) (coe v7)
                             (coe
                                d_state_84
                                (coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2))))))
             MAlonzo.Code.Once.Arith.IR.C_Mod_124 v3 v4 v6 v7
               -> coe du_compile'45'float_454 (coe v0) (coe v6) (coe v2)
             MAlonzo.Code.Once.Arith.IR.C_Neg_130 v5
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v5) (coe v2)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_allocGPR_32
                                      (coe
                                         d_state_84
                                         (coe du_compile'45'float_454 (coe v0) (coe v5) (coe v2)))))
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_immI_142
                                   (coe (9223372036854775808 :: Integer)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movqToXMM_216
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_allocXMM_38
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_allocGPR_32
                                               (coe
                                                  d_state_84
                                                  (coe
                                                     du_compile'45'float_454 (coe v0) (coe v5)
                                                     (coe v2)))))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_allocGPR_32
                                         (coe
                                            d_state_84
                                            (coe
                                               du_compile'45'float_454 (coe v0) (coe v5)
                                               (coe v2)))))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorpd_214
                                      (coe
                                         d_result_82
                                         (coe du_compile'45'float_454 (coe v0) (coe v5) (coe v2)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_allocXMM_38
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_allocGPR_32
                                                  (coe
                                                     d_state_84
                                                     (coe
                                                        du_compile'45'float_454 (coe v0) (coe v5)
                                                        (coe v2)))))))))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v5) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_freeGPR_44
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_allocXMM_38
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_allocGPR_32
                                      (coe
                                         d_state_84
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v5)
                                            (coe v2)))))))))
             MAlonzo.Code.Once.Arith.IR.C_Cmp_138 v3 v4 v6 v7 v8
               -> coe
                    C_mkFloatResult_86
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_code_80 (coe du_compile'45'float_454 (coe v0) (coe v7) (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_code_80
                             (coe
                                du_compile'45'float_454 (coe v0) (coe v8)
                                (coe
                                   d_state_84
                                   (coe du_compile'45'float_454 (coe v0) (coe v7) (coe v2)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_subsd_206
                                   (coe
                                      d_result_82
                                      (coe du_compile'45'float_454 (coe v0) (coe v7) (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146
                                      (coe
                                         d_result_82
                                         (coe
                                            du_compile'45'float_454 (coe v0) (coe v8)
                                            (coe
                                               d_state_84
                                               (coe
                                                  du_compile'45'float_454 (coe v0) (coe v7)
                                                  (coe v2))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       d_result_82
                       (coe du_compile'45'float_454 (coe v0) (coe v7) (coe v2)))
                    (coe
                       d_freeXMM_50
                       (coe
                          d_state_84
                          (coe
                             du_compile'45'float_454 (coe v0) (coe v8)
                             (coe
                                d_state_84
                                (coe du_compile'45'float_454 (coe v0) (coe v7) (coe v2))))))
             MAlonzo.Code.Once.Arith.IR.C_Conv_146 v4 v6
               -> case coe v4 of
                    MAlonzo.Code.Once.Arith.Type.C_I8_8
                      -> coe
                           C_mkFloatResult_86
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorpd_214
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe d_allocXMM_38 (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_allocXMM_38 (coe v2)))
                    MAlonzo.Code.Once.Arith.Type.C_I16_10
                      -> coe
                           C_mkFloatResult_86
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorpd_214
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe d_allocXMM_38 (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_allocXMM_38 (coe v2)))
                    MAlonzo.Code.Once.Arith.Type.C_I32_12
                      -> coe
                           C_mkFloatResult_86
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorpd_214
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe d_allocXMM_38 (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_allocXMM_38 (coe v2)))
                    MAlonzo.Code.Once.Arith.Type.C_I64_14
                      -> coe
                           C_mkFloatResult_86
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xorpd_214
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe d_allocXMM_38 (coe v2)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe d_allocXMM_38 (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_allocXMM_38 (coe v2)))
                    MAlonzo.Code.Once.Arith.Type.C_F32_16
                      -> coe
                           C_mkFloatResult_86
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 d_code_80 (coe du_compile'45'float_454 (coe v4) (coe v6) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                                    (coe
                                       MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_cvtss2sd_218
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_allocXMM_38
                                             (coe
                                                d_state_84
                                                (coe
                                                   du_compile'45'float_454 (coe v4) (coe v6)
                                                   (coe v2)))))
                                       (coe
                                          d_result_82
                                          (coe
                                             du_compile'45'float_454 (coe v4) (coe v6) (coe v2)))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_allocXMM_38
                                 (coe
                                    d_state_84
                                    (coe du_compile'45'float_454 (coe v4) (coe v6) (coe v2)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe
                                 d_allocXMM_38
                                 (coe
                                    d_state_84
                                    (coe du_compile'45'float_454 (coe v4) (coe v6) (coe v2)))))
                    MAlonzo.Code.Once.Arith.Type.C_F64_18
                      -> coe du_compile'45'float_454 (coe v4) (coe v6) (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.compile-arith
d_compile'45'arith_878 ::
  [MAlonzo.Code.Once.Arith.IR.T_Binding_6] ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.IR.T_ArithIR_72 ->
  [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithInstr_220]
d_compile'45'arith_878 ~v0 v1 v2 = du_compile'45'arith_878 v1 v2
du_compile'45'arith_878 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.IR.T_ArithIR_72 ->
  [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithInstr_220]
du_compile'45'arith_878 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Type.C_I8_8
        -> let v2
                 = coe
                     du_compile'45'int_106 (coe v0) (coe v1) (coe d_initAlloc_26) in
           coe
             (case coe v2 of
                C_mkIntResult_70 v3 v4 v5
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                                (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rax_12)
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138 (coe v4))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Type.C_I16_10
        -> let v2
                 = coe
                     du_compile'45'int_106 (coe v0) (coe v1) (coe d_initAlloc_26) in
           coe
             (case coe v2 of
                C_mkIntResult_70 v3 v4 v5
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                                (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rax_12)
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138 (coe v4))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Type.C_I32_12
        -> let v2
                 = coe
                     du_compile'45'int_106 (coe v0) (coe v1) (coe d_initAlloc_26) in
           coe
             (case coe v2 of
                C_mkIntResult_70 v3 v4 v5
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                                (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rax_12)
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138 (coe v4))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Type.C_I64_14
        -> let v2
                 = coe
                     du_compile'45'int_106 (coe v0) (coe v1) (coe d_initAlloc_26) in
           coe
             (case coe v2 of
                C_mkIntResult_70 v3 v4 v5
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_intI_222
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movI_166
                                (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_rax_12)
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regI_138 (coe v4))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Type.C_F32_16
        -> let v2
                 = coe
                     du_compile'45'float_454 (coe v0) (coe v1) (coe d_initAlloc_26) in
           coe
             (case coe v2 of
                C_mkFloatResult_86 v3 v4 v5
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movss_192
                                (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm0_92)
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146 (coe v4))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Type.C_F64_18
        -> let v2
                 = coe
                     du_compile'45'float_454 (coe v0) (coe v1) (coe d_initAlloc_26) in
           coe
             (case coe v2 of
                C_mkFloatResult_86 v3 v4 v5
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_floatI_224
                             (coe
                                MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_movsd_194
                                (coe MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_xmm0_92)
                                (coe
                                   MAlonzo.Code.Once.Arith.Backend.X86.Syntax.C_regF_146 (coe v4))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86.CodeGen.code-length
d_code'45'length_952 ::
  [MAlonzo.Code.Once.Arith.Backend.X86.Syntax.T_ArithInstr_220] ->
  Integer
d_code'45'length_952
  = coe MAlonzo.Code.Data.List.Base.du_length_268
-- Once.Arith.Backend.X86.CodeGen.compile-lit-int-char
d_compile'45'lit'45'int'45'char_960 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'lit'45'int'45'char_960 = erased
