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
import qualified MAlonzo.Code.Once.Functor.Translate
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
    C__'8728'__30 MAlonzo.Code.Once.Type.T_Type_112 T_IR_16 T_IR_16 |
    C_'10216'_'44'_'10217'_38 T_IR_16 T_IR_16 T_AllocMode_4 |
    C_fst_44 | C_snd_50 | C_inl_56 T_AllocMode_4 |
    C_inr_62 T_AllocMode_4 | C_case_70 T_IR_16 T_IR_16 |
    C_terminal_74 | C_initial_78 | C_curry_88 T_IR_16 T_AllocMode_4 |
    C_apply_96 | C_arr_104 |
    C_In_108 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
             T_AllocMode_4 |
    C_out'45'μ_112 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 |
    C_Cata_118 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               T_IR_16 |
    C_Para_124 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               T_IR_16 |
    C_Out_128 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 |
    C_in'45'ν_132 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                  T_AllocMode_4 |
    C_Ana_138 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
              T_IR_16 |
    C_Hylo_146 MAlonzo.Code.Once.Type.T_Functor_110
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 T_IR_16
               T_NatTr_18 |
    C_Fuse_154 MAlonzo.Code.Once.Type.T_Functor_110
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 T_IR_16
               T_NatTr_18 |
    C_free'45'heap_156 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 |
    C_const_160 MAlonzo.Code.Once.Type.T_FitsInReg_192 AgdaAny |
    C_SigOp_166 MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_134
-- Once.IR.NatTr
d_NatTr_18 a0 a1 = ()
data T_NatTr_18
  = C_ntId_168 | C_ntK_174 T_IR_16 | C_ntFst_182 T_NatTr_18 |
    C_ntSnd_190 T_NatTr_18 | C_ntCase_198 T_NatTr_18 T_NatTr_18 |
    C_ntInl_206 T_NatTr_18 | C_ntInr_214 T_NatTr_18 |
    C_ntPair_222 T_NatTr_18 T_NatTr_18
