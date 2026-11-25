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

module MAlonzo.Code.Once.Surface.Map where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Surface.Map.Map
d_Map_8 a0 a1 a2 = ()
data T_Map_8
  = C_mp'45'id_14 | C_mp'45'fst_20 | C_mp'45'snd_26 |
    C_mp'45'terminal_30 | C_mp'45'inl_36 | C_mp'45'inr_42 |
    C_mp'45'initial_46 | C_mp'45'apply_54 |
    C_mp'45'In_60 (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                   MAlonzo.Code.Once.Spec.Type.T_Kind_70)
                  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 |
    C_mp'45'Out_68 (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                    MAlonzo.Code.Once.Spec.Type.T_Kind_70)
                   MAlonzo.Code.Once.Spec.Type.T_WFFun_118 |
    C_mp'45'toFloat_70
