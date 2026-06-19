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

module MAlonzo.Code.Once.CCC.IR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.IR.AllocMode
d_AllocMode_6 = ()
data T_AllocMode_6 = C_Stack_8 | C_Heap_10
-- Once.CCC.IR.Allocator
d_Allocator_12 = ()
data T_Allocator_12
  = C_Stack'45'allocator_14 | C_Dynamic'45'allocator_16
-- Once.CCC.IR.IR
d_IR_18 a0 a1 = ()
data T_IR_18
  = C_id_24 |
    C__'8728'__32 MAlonzo.Code.Once.Type.T_Type_112 T_IR_18 T_IR_18 |
    C_'10216'_'44'_'10217'_40 T_IR_18 T_IR_18 T_AllocMode_6 |
    C_fst_46 | C_snd_52 | C_inl_58 T_AllocMode_6 |
    C_inr_64 T_AllocMode_6 | C_case_72 T_IR_18 T_IR_18 |
    C_terminal_76 | C_initial_80 | C_curry_90 T_IR_18 T_AllocMode_6 |
    C_apply_98 | C_arr_106 |
    C_In_110 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
             T_AllocMode_6 |
    C_out'45'μ_114 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 |
    C_Cata_120 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               T_IR_18 |
    C_Para_126 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               T_IR_18 |
    C_Out_130 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 |
    C_in'45'ν_134 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                  T_AllocMode_6 |
    C_Ana_140 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
              T_IR_18 |
    C_Hylo_148 MAlonzo.Code.Once.Type.T_Functor_110
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 T_IR_18
               T_NatTr_20 |
    C_Fuse_156 MAlonzo.Code.Once.Type.T_Functor_110
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 T_IR_18
               T_NatTr_20 |
    C_free'45'heap_158 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 |
    C_const_162 MAlonzo.Code.Once.Type.T_FitsInReg_192 AgdaAny |
    C_SigOp_168 MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
-- Once.CCC.IR.NatTr
d_NatTr_20 a0 a1 = ()
data T_NatTr_20
  = C_ntId_170 | C_ntK_176 T_IR_18 | C_ntFst_184 T_NatTr_20 |
    C_ntSnd_192 T_NatTr_20 | C_ntCase_200 T_NatTr_20 T_NatTr_20 |
    C_ntInl_208 T_NatTr_20 | C_ntInr_216 T_NatTr_20 |
    C_ntPair_224 T_NatTr_20 T_NatTr_20
