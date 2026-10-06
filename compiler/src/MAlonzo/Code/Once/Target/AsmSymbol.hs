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

module MAlonzo.Code.Once.Target.AsmSymbol where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base

-- Once.Target.AsmSymbol.sym-punct
d_sym'45'punct_6 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_sym'45'punct_6 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         eqInt (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
         (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 '_'))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            eqInt (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
            (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 '.'))
         (coe
            eqInt (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
            (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 '$')))
-- Once.Target.AsmSymbol.sym-start
d_sym'45'start_10 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_sym'45'start_10 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
      (coe d_sym'45'punct_6 (coe v0))
-- Once.Target.AsmSymbol.sym-continue
d_sym'45'continue_14 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_sym'45'continue_14 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe d_sym'45'start_10 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v0)
-- Once.Target.AsmSymbol.AsmSymChars
d_AsmSymChars_18 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_AsmSymChars_18 = erased
-- Once.Target.AsmSymbol.AsmSym
d_AsmSym_26 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_AsmSym_26 = erased
