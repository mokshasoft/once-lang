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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.IR.AllocMode
d_AllocMode_6 = ()
data T_AllocMode_6 = C_Stack_8 | C_Heap_10
-- Once.CCC.IR.IR
d_IR_12 a0 a1 = ()
data T_IR_12
  = C_id_16 |
    C__'8728'__24 MAlonzo.Code.Once.Type.T_Type_38 T_IR_12 T_IR_12 |
    C_'10216'_'44'_'10217'_32 T_IR_12 T_IR_12 T_AllocMode_6 |
    C_fst_38 | C_snd_44 | C_inl_50 T_AllocMode_6 |
    C_inr_56 T_AllocMode_6 | C_case_64 T_IR_12 T_IR_12 |
    C_terminal_68 | C_initial_72 | C_curry_82 T_IR_12 T_AllocMode_6 |
    C_apply_90 | C_arr_98 | C_applyEff_104 |
    C_In_108 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176
             T_AllocMode_6 |
    C_out'45'μ_112 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 |
    C_Cata_118 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176
               T_IR_12 |
    C_Para_124 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176
               T_IR_12 |
    C_Out_128 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 |
    C_in'45'ν_132 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176
                  T_AllocMode_6 |
    C_Ana_138 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176
              T_IR_12 |
    C_Hylo_146 MAlonzo.Code.Once.Type.T_Functor_36
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 T_IR_12
               T_IR_12 |
    C_Fuse_154 MAlonzo.Code.Once.Type.T_Functor_36
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176
               MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 T_IR_12
               T_IR_12 |
    C_free'45'heap_156 MAlonzo.Code.Once.CCC.Machine.SMCore.T_HeapRef_20 |
    C_Prim_162 MAlonzo.Code.Agda.Builtin.String.T_String_6
