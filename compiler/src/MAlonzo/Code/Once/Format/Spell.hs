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

module MAlonzo.Code.Once.Format.Spell where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Spec.Surface.Lexing

-- Once.Format.Spell.showInt
d_showInt_6 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showInt_6 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0
      _ -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("-" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.Nat.Show.d_show_56
                (subInt (coe (0 :: Integer)) (coe v0)))
-- Once.Format.Spell.showFloat
d_showFloat_12 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFloat_12 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("." :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (coe
               MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
               (coe
                  MAlonzo.Code.Data.List.Base.du_replicate_278
                  (coe
                     MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
                     (MAlonzo.Code.Data.String.Base.d_length_22
                        (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)))
                  (coe '0')))
            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)))
-- Once.Format.Spell.spell
d_spell_20 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_spell_20 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TWord_10 v1 -> coe v1
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TInt_12 v1
        -> coe d_showInt_6 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TFloat_14 v1 v2 v3
        -> coe d_showFloat_12 (coe v1) (coe v2) (coe v3)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TString_16 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\"" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                ("\"" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18
        -> coe ("(" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20
        -> coe (")" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLBrace_22
        -> coe ("{" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRBrace_24
        -> coe ("}" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TColon_26
        -> coe (":" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEquals_28
        -> coe ("=" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30
        -> coe ("->" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TCaret1_32
        -> coe ("^1" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TCaret0_34
        -> coe ("^0" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TCaretW_36
        -> coe ("^w" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLambda_38
        -> coe ("\\" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TComma_40
        -> coe ("," :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TSemicolon_42
        -> coe (";" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TAt_44
        -> coe ("@" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPipe_46
        -> coe ("|" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48
        -> coe ("." :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPlus_50
        -> coe ("+" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TMinus_52
        -> coe ("-" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TStar_54
        -> coe ("*" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TSlash_56
        -> coe ("/" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPercent_58
        -> coe ("%" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TAmpersand_60
        -> coe ("&" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLt_62
        -> coe ("<" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLe_64
        -> coe ("<=" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TGt_66
        -> coe (">" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TGe_68
        -> coe (">=" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEqEq_70
        -> coe ("==" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TNeq_72
        -> coe ("!=" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TBang_74
        -> coe ("!" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TNewline_76
        -> coe ("\n" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEOF_78
        -> coe ("" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
