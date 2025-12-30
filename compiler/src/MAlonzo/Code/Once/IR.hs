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
import qualified MAlonzo.Code.Agda.Builtin.Size
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.IR.IR
d_IR_4 a0 a1 a2 = ()
data T_IR_4
  = C_id_10 |
    C__'8728'__20 MAlonzo.Code.Once.Type.T_Type_4 T_IR_4 T_IR_4 |
    C_fst_28 | C_snd_36 | C_'10216'_'44'_'10217'_46 T_IR_4 T_IR_4 |
    C_inl_54 | C_inr_62 | C_'91'_'44'_'93'_72 T_IR_4 T_IR_4 |
    C_terminal_78 | C_initial_84 | C_curry_94 T_IR_4 | C_apply_102 |
    C_fold_108 | C_unfold_114 | C_arr_122 | C_intLit_128 Integer |
    C_binOp_134 MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 |
    C_prim_142 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.IR.IR∞
d_IR'8734'_144 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> ()
d_IR'8734'_144 = erased
