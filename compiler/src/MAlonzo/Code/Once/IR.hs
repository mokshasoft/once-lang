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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Type

-- Once.IR.AllocMode
d_AllocMode_4 = ()
data T_AllocMode_4 = C_Stack_6 | C_Heap_8
-- Once.IR.IR
d_IR_10 a0 a1 = ()
data T_IR_10
  = C_id_14 |
    C__'8728'__22 MAlonzo.Code.Once.Type.T_Type_32 T_IR_10 T_IR_10 |
    C_fst_28 | C_snd_34 |
    C_'10216'_'44'_'10217'_42 T_IR_10 T_IR_10 T_AllocMode_4 |
    C_inl_48 T_AllocMode_4 | C_inr_54 T_AllocMode_4 |
    C_'91'_'44'_'93'_62 T_IR_10 T_IR_10 | C_terminal_66 |
    C_initial_70 | C_curry_80 T_IR_10 T_AllocMode_4 | C_apply_88 |
    C_fold_92 | C_unfold_96 | C_arr_102 |
    C_Prim_108 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.IR.IR∞
d_IR'8734'_110 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> ()
d_IR'8734'_110 = erased
