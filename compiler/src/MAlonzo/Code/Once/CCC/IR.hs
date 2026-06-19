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
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.IR.AllocMode
d_AllocMode_6 = ()
data T_AllocMode_6 = C_Stack_8 | C_Heap_10
-- Once.CCC.IR.LocMatchesMode
d_LocMatchesMode_14 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocMode_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_LocMatchesMode_14 = erased
-- Once.CCC.IR.Allocator
d_Allocator_16 = ()
data T_Allocator_16
  = C_Stack'45'allocator_18 | C_Dynamic'45'allocator_20
-- Once.CCC.IR.IR
d_IR_22 a0 a1 = ()
data T_IR_22
  = C_id_28 |
    C__'8728'__36 MAlonzo.Code.Once.Type.T_Type_112 T_IR_22 T_IR_22 |
    C_'10216'_'44'_'10217'_44 T_IR_22 T_IR_22 T_AllocMode_6 |
    C_fst_50 | C_snd_56 | C_inl_62 T_AllocMode_6 |
    C_inr_68 T_AllocMode_6 | C_case_76 T_IR_22 T_IR_22 |
    C_terminal_80 | C_initial_84 | C_curry_94 T_IR_22 T_AllocMode_6 |
    C_apply_102 | C_arr_110 |
    C_In_114 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
             T_AllocMode_6 |
    C_out'45'μ_118 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 |
    C_Cata_124 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               T_IR_22 |
    C_Para_130 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               T_IR_22 |
    C_Out_134 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 |
    C_in'45'ν_138 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
                  T_AllocMode_6 |
    C_Ana_144 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
              T_IR_22 |
    C_Hylo_152 MAlonzo.Code.Once.Type.T_Functor_110
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 T_IR_22
               T_NatTr_24 |
    C_Fuse_160 MAlonzo.Code.Once.Type.T_Functor_110
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 T_IR_22
               T_NatTr_24 |
    C_free'45'heap_162 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 |
    C_const_166 MAlonzo.Code.Once.Type.T_FitsInReg_192 AgdaAny |
    C_SigOp_172 MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_136
-- Once.CCC.IR.NatTr
d_NatTr_24 a0 a1 = ()
data T_NatTr_24
  = C_ntId_174 | C_ntK_180 T_IR_22 | C_ntFst_188 T_NatTr_24 |
    C_ntSnd_196 T_NatTr_24 | C_ntCase_204 T_NatTr_24 T_NatTr_24 |
    C_ntInl_212 T_NatTr_24 | C_ntInr_220 T_NatTr_24 |
    C_ntPair_228 T_NatTr_24 T_NatTr_24
