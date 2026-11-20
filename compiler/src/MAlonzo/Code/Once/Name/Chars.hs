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

module MAlonzo.Code.Once.Name.Chars where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.ListAction

-- Once.Name.Chars.toNat
d_toNat_6 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Integer
d_toNat_6 = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
-- Once.Name.Chars.isIdentStart
d_isIdentStart_8 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isIdentStart_8 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
      (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '_'))
-- Once.Name.Chars.isIdentContinue
d_isIdentContinue_12 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isIdentContinue_12 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v0)
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '_'))
            (coe
               MAlonzo.Code.Data.Bool.Base.d__'8744'__30
               (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '\''))
               (coe
                  MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                  (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '+'))
                  (coe
                     MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                     (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '*'))
                     (coe
                        MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                        (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '!'))
                        (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '?'))))))))
-- Once.Name.Chars.opNameChars
d_opNameChars_16 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_opNameChars_16
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '.')
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '+')
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '-')
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '*')
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '/')
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '%')
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '<')
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '>')
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '|')
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '&')
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '@')
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
-- Once.Name.Chars.isOpNameChar
d_isOpNameChar_18 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isOpNameChar_18 v0
  = coe
      MAlonzo.Code.Data.Bool.ListAction.du_any_14
      (coe (\ v1 -> eqInt (coe d_toNat_6 v0) (coe d_toNat_6 v1)))
      (coe d_opNameChars_16)
