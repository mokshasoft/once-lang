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

module MAlonzo.Code.Agda.Builtin.Size where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

type SizeLT i = ()
-- Agda.Builtin.Size.SizeUniv
d_SizeUniv_6 :: ()
d_SizeUniv_6 = erased
-- Agda.Builtin.Size.Size
type T_Size_8 = ()
d_Size_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Builtin.Size.Size"
-- Agda.Builtin.Size.Size<_
type T_Size'60'__10 a0 = SizeLT a0
d_Size'60'__10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Builtin.Size.Size<_"
-- Agda.Builtin.Size.↑_
d_'8593'__12 :: T_Size_8 -> T_Size_8
d_'8593'__12 = \_ -> ()
-- Agda.Builtin.Size.∞
d_'8734'_14 :: T_Size_8
d_'8734'_14 = ()
-- Agda.Builtin.Size._⊔ˢ_
d__'8852''738'__16 :: T_Size_8 -> T_Size_8 -> T_Size_8
d__'8852''738'__16 = \_ _ -> ()
