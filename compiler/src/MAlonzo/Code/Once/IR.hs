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
    C_Cata_108 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_IR_16 |
    C_Para_114 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_IR_16 |
    C_Out_118 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 |
    C_in'45'ν_122 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
                  T_AllocMode_4 |
    C_Ana_128 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_IR_16 |
    C_Hylo_136 MAlonzo.Code.Once.IRTy.T_IRFunctor_4
               MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
               MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_IR_16 T_NatTr_18 |
    C_Fuse_144 MAlonzo.Code.Once.IRTy.T_IRFunctor_4
               MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
               MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 T_IR_16 T_NatTr_18 |
    C_free'45'heap_146 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 |
    C_const_150 MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 AgdaAny |
    C_SigOp_156 MAlonzo.Code.Once.Type.T_Type_108
                MAlonzo.Code.Once.Type.T_Type_108
                MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
-- Once.IR.NatTr
d_NatTr_18 a0 a1 = ()
data T_NatTr_18
  = C_ntId_158 | C_ntK_164 T_IR_16 | C_ntFst_172 T_NatTr_18 |
    C_ntSnd_180 T_NatTr_18 | C_ntCase_188 T_NatTr_18 T_NatTr_18 |
    C_ntInl_196 T_NatTr_18 | C_ntInr_204 T_NatTr_18 |
    C_ntPair_212 T_NatTr_18 T_NatTr_18
