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
import qualified MAlonzo.Code.Once.Type

-- Once.IR.IR
d_IR_4 a0 a1 = ()
data T_IR_4
  = C_id_8 |
    C__'8728'__16 MAlonzo.Code.Once.Type.T_Type_4 T_IR_4 T_IR_4 |
    C_fst_22 | C_snd_28 | C_'10216'_'44'_'10217'_36 T_IR_4 T_IR_4 |
    C_inl_42 | C_inr_48 | C_'91'_'44'_'93'_56 T_IR_4 T_IR_4 |
    C_terminal_60 | C_initial_64 | C_curry_72 T_IR_4 | C_apply_78 |
    C_fold_82 | C_unfold_86 | C_arr_92
