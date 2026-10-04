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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IRTy
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
  = C_id_20 |
    C__'8728'__28 MAlonzo.Code.Once.IRTy.T_IRTy_6 T_IR_16 T_IR_16 |
    C_'10216'_'44'_'10217'_36 T_IR_16 T_IR_16 | C_fst_42 | C_snd_48 |
    C_inl_54 | C_inr_60 | C_case_68 T_IR_16 T_IR_16 | C_terminal_72 |
    C_initial_76 | C_curry_84 T_IR_16 | C_apply_90 |
    C_In_94 MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 |
    C_out'45'μ_98 MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 |
    C_Cata_106 MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 T_IR_16 |
    C_Out_110 MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 |
    C_in'45'ν_114 MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 |
    C_Ana_120 MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 T_IR_16 |
    C_const_124 MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 AgdaAny |
    C_SigOp_130 MAlonzo.Code.Once.Type.T_Type_108
                MAlonzo.Code.Once.Type.T_Type_108
                MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 |
    C_Call_136 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
