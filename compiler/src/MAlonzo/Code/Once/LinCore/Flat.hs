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

module MAlonzo.Code.Once.LinCore.Flat where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.LinCore.Flat.FTy
d_FTy_8 a0 = ()
data T_FTy_8
  = C_funit_12 | C_fvoid_14 | C_fw_16 AgdaAny |
    C__f'42'__18 T_FTy_8 T_FTy_8 | C__f'43'__20 T_FTy_8 T_FTy_8
-- Once.LinCore.Flat.⟦_⟧F
d_'10214'_'10215'F_24 :: () -> (AgdaAny -> ()) -> T_FTy_8 -> ()
d_'10214'_'10215'F_24 = erased
-- Once.LinCore.Flat.Base
d_Base_46 = ()
data T_Base_46 = C_int_48 | C_float_50
-- Once.LinCore.Flat.⟦_⟧b
d_'10214'_'10215'b_52 :: T_Base_46 -> ()
d_'10214'_'10215'b_52 = erased
-- Once.LinCore.Flat.Lit
d_Lit_54 :: T_Base_46 -> ()
d_Lit_54 = erased
