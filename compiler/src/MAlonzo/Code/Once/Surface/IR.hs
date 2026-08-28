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

module MAlonzo.Code.Once.Surface.IR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.IR.SurfaceIR
d_SurfaceIR_6 a0 a1 = ()
data T_SurfaceIR_6
  = C_id_10 |
    C__'8728'__18 MAlonzo.Code.Once.Type.T_Type_108 T_SurfaceIR_6
                  T_SurfaceIR_6 |
    C_fst_24 | C_snd_30 |
    C_'10216'_'44'_'10217'_38 T_SurfaceIR_6 T_SurfaceIR_6 | C_inl_44 |
    C_inr_50 | C_'91'_'44'_'93'_58 T_SurfaceIR_6 T_SurfaceIR_6 |
    C_terminal_62 | C_initial_66 | C_curry_74 T_SurfaceIR_6 |
    C_apply_80 | C_arr_86 |
    C_Let_94 MAlonzo.Code.Once.Type.T_Type_108 T_SurfaceIR_6
             T_SurfaceIR_6 |
    C_SigOp_100 MAlonzo.Code.Agda.Builtin.String.T_String_6
                MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
                MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
