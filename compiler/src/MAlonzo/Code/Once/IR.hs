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

module MAlonzo.Code.Once.IR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.IR.AllocMode
d_AllocMode_4 = ()
data T_AllocMode_4 = C_Stack_6 | C_Heap_8
-- Once.IR.Allocator
d_Allocator_10 = ()
data T_Allocator_10
  = C_Stack'45'allocator_12 | C_Dynamic'45'allocator_14
-- Once.IR.IR
d_IR_16 a0 a1 = ()
data T_IR_16
  = C_id_22 |
    C__'8728'__30 MAlonzo.Code.Once.IRTy.T_IRTy_6 T_IR_16 T_IR_16 |
    C_'10216'_'44'_'10217'_38 T_IR_16 T_IR_16 T_AllocMode_4 |
    C_fst_44 | C_snd_50 | C_inl_56 T_AllocMode_4 |
    C_inr_62 T_AllocMode_4 | C_case_70 T_IR_16 T_IR_16 |
    C_terminal_74 | C_initial_78 | C_curry_86 T_IR_16 T_AllocMode_4 |
    C_apply_92 |
    C_In_96 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_AllocMode_4 |
    C_out'45'μ_100 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 |
    C_Cata_106 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_IR_16 |
    C_Para_112 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_IR_16 |
    C_Out_116 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 |
    C_in'45'ν_120 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
                  T_AllocMode_4 |
    C_Ana_126 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_IR_16 |
    C_Hylo_134 MAlonzo.Code.Once.IRTy.T_IRFunctor_4
               MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
               MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_IR_16 T_NatTr_18 |
    C_Fuse_142 MAlonzo.Code.Once.IRTy.T_IRFunctor_4
               MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
               MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_IR_16 T_NatTr_18 |
    C_free'45'heap_144 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 |
    C_const_148 MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 AgdaAny |
    C_SigOp_154 MAlonzo.Code.Once.Type.T_Type_108
                MAlonzo.Code.Once.Type.T_Type_108
                MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
-- Once.IR.NatTr
d_NatTr_18 a0 a1 = ()
data T_NatTr_18
  = C_ntId_156 | C_ntK_162 T_IR_16 | C_ntFst_170 T_NatTr_18 |
    C_ntSnd_178 T_NatTr_18 | C_ntCase_186 T_NatTr_18 T_NatTr_18 |
    C_ntInl_194 T_NatTr_18 | C_ntInr_202 T_NatTr_18 |
    C_ntPair_210 T_NatTr_18 T_NatTr_18
