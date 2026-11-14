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

module MAlonzo.Code.Once.Format.Lex where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Surface.Operator

-- Once.Format.Lex.Item
d_Item_6 = ()
data T_Item_6
  = C_tok_8 MAlonzo.Code.Once.Parser.Token.T_Token_6 |
    C_comment_10 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_cont_12
-- Once.Format.Lex.tokensOf
d_tokensOf_14 ::
  [T_Item_6] -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokensOf_14 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             C_tok_8 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                    (coe d_tokensOf_14 (coe v2))
             C_comment_10 v3 -> coe d_tokensOf_14 (coe v2)
             C_cont_12 -> coe d_tokensOf_14 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Lex.consumed
d_consumed_24 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_consumed_24 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_take_530
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
         (coe MAlonzo.Code.Data.List.Base.du_length_268 v1))
      (coe v0)
-- Once.Format.Lex.items-WF
d_items'45'WF_34 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> [T_Item_6]
d_items'45'WF_34 v0 v1 ~v2 = du_items'45'WF_34 v0 v1
du_items'45'WF_34 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer -> [T_Item_6]
du_items'45'WF_34 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TEOF_58))
             (coe v0)
      (:) v2 v3
        -> coe
             du_it'45'head_44 (coe v2) (coe v3) (coe v1)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_headK_516 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Lex.it-head
d_it'45'head_44 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Parser.Lexer.T_HeadK_462 -> [T_Item_6]
d_it'45'head_44 v0 v1 v2 ~v3 v4 = du_it'45'head_44 v0 v1 v2 v4
du_it'45'head_44 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> MAlonzo.Code.Once.Parser.Lexer.T_HeadK_462 -> [T_Item_6]
du_it'45'head_44 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.Lexer.C_hkWS_464
        -> coe
             du_items'45'WF_34 (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                (coe v2))
      MAlonzo.Code.Once.Parser.Lexer.C_hkNL_466
        -> coe
             du_it'45'nl_92 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_nlIndent_428 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkCaret_468
        -> coe
             du_it'45'caret_142 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_caretClass_448 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkDash_470
        -> coe
             du_it'45'minus_134 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_dashClass_444 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkLBrace_472
        -> coe
             du_it'45'lbrace_126 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isDashHead_440 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkLt_474
        -> coe
             du_it'45'cmp_110 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'60''61'_20)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'60'_18)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_432 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkGt_476
        -> coe
             du_it'45'cmp_110 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62''61'_24)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62'_22)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_432 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkEq_478
        -> coe
             du_it'45'eqop_118 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'61''61'_26)
             (coe MAlonzo.Code.Once.Parser.Token.C_TEquals_26)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_432 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkBang_480
        -> coe
             du_it'45'eqop_118 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'33''61'_28)
             (coe MAlonzo.Code.Once.Parser.Token.C_TBang_54)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_432 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkLParen_482
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkRParen_484
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkRBrace_486
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TRBrace_22))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkColon_488
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TColon_24))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkLambda_490
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TLambda_36))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkComma_492
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TComma_38))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkSemi_494
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkAt_496
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TAt_42))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkPipe_498
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TPipe_44))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkPlus_500
        -> coe
             du_it'45'dot_102 (coe v1) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'43'_10)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isDotHead_436 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkStar_502
        -> coe
             du_it'45'dot_102 (coe v1) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'42'_14)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isDotHead_436 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkSlash_504
        -> coe
             du_it'45'dot_102 (coe v1) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'47'_16)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isDotHead_436 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkPct_506
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                C_tok_8
                (coe
                   MAlonzo.Code.Once.Parser.Token.C_TOp_48
                   (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'37'_34)))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkAmp_508
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TAmpersand_52))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkDot_510
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TDot_46))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v1)
                   (coe v2)))
      MAlonzo.Code.Once.Parser.Lexer.C_hkStr_512
        -> coe
             du_it'45'str_56 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_collectStringB_168 (coe v1))
      MAlonzo.Code.Once.Parser.Lexer.C_hkGen_514
        -> coe
             du_it'45'gen_66 (coe v0) (coe v1) (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v0)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentStart_8 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Lex.it-str
d_it'45'str_56 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_Item_6]
d_it'45'str_56 v0 v1 ~v2 v3 = du_it'45'str_56 v0 v1 v3
du_it'45'str_56 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_Item_6]
du_it'45'str_56 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              C_tok_8
                              (coe
                                 MAlonzo.Code.Once.Parser.Token.C_TString_14
                                 (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14 v4)))
                           (coe
                              du_items'45'WF_34 (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0) (coe v6)
                                 (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Lex.it-gen
d_it'45'gen_66 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> Bool -> [T_Item_6]
d_it'45'gen_66 v0 v1 v2 ~v3 v4 v5 = du_it'45'gen_66 v0 v1 v2 v4 v5
du_it'45'gen_66 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> Bool -> [T_Item_6]
du_it'45'gen_66 v0 v1 v2 v3 v4
  = if coe v3
      then coe
             du_it'45'num_84 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_80 (coe v1)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_80 (coe v1))))
             (coe
                MAlonzo.Code.Once.Parser.Lexer.d_collectFracB_110
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_80 (coe v1)))))
      else (if coe v4
              then coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        C_tok_8
                        (coe
                           MAlonzo.Code.Once.Parser.Token.C_TWord_8
                           (coe
                              MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.Parser.Lexer.d_collectIdentB_46
                                       (coe v1)))))))
                     (coe
                        du_items'45'WF_34
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe MAlonzo.Code.Once.Parser.Lexer.d_collectIdentB_46 (coe v1))))
                        (coe
                           MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe MAlonzo.Code.Once.Parser.Lexer.d_collectIdentB_46 (coe v1))))
                           (coe v2)))
              else coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Format.Lex.it-num
d_it'45'num_84 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_Item_6]
d_it'45'num_84 v0 v1 v2 ~v3 v4 v5 ~v6 v7
  = du_it'45'num_84 v0 v1 v2 v4 v5 v7
du_it'45'num_84 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_Item_6]
du_it'45'num_84 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              C_tok_8
                              (coe
                                 MAlonzo.Code.Once.Parser.Token.C_TFloat_12
                                 (coe
                                    MAlonzo.Code.Once.Parser.Lexer.d_digitsToNat_160
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                                       (coe v3)))
                                 (coe MAlonzo.Code.Once.Parser.Lexer.d_digitsToNat_160 v7)
                                 (coe MAlonzo.Code.Data.List.Base.du_length_268 v7) (coe v2)))
                           (coe
                              du_items'45'WF_34 (coe v9)
                              (coe
                                 MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v9)
                                 (coe v2)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                C_tok_8
                (coe
                   MAlonzo.Code.Once.Parser.Token.C_TInt_10
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_digitsToNat_160
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
                   (coe v2)))
             (coe
                du_items'45'WF_34 (coe v4)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v1) (coe v4)
                   (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Lex.it-nl
d_it'45'nl_92 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> [T_Item_6]
d_it'45'nl_92 v0 v1 ~v2 v3 = du_it'45'nl_92 v0 v1 v3
du_it'45'nl_92 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> [T_Item_6]
du_it'45'nl_92 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_cont_12)
             (coe
                du_items'45'WF_34 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0) (coe v0)
                   (coe v1)))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_56))
             (coe
                du_items'45'WF_34 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Format.Lex.it-dot
d_it'45'dot_102 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  Bool -> [T_Item_6]
d_it'45'dot_102 v0 v1 v2 ~v3 ~v4 v5 v6
  = du_it'45'dot_102 v0 v1 v2 v5 v6
du_it'45'dot_102 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  Bool -> [T_Item_6]
du_it'45'dot_102 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TOpD_50 (coe v3)))
             (coe
                du_items'45'WF_34
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v1))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v1))
                   (coe v2)))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                C_tok_8
                (coe
                   MAlonzo.Code.Once.Parser.Token.C_TOp_48
                   (coe
                      MAlonzo.Code.Once.Spec.Surface.Operator.C_'8249'_'8250'_32
                      (coe v3))))
             (coe
                du_items'45'WF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0) (coe v1)
                   (coe v2)))
-- Once.Format.Lex.it-cmp
d_it'45'cmp_110 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  Bool -> [T_Item_6]
d_it'45'cmp_110 v0 v1 ~v2 v3 v4 v5
  = du_it'45'cmp_110 v0 v1 v3 v4 v5
du_it'45'cmp_110 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  Bool -> [T_Item_6]
du_it'45'cmp_110 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_it'45'dot_102 (coe v0)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0)) (coe v1)
             (coe v2)
             (coe
                MAlonzo.Code.Once.Parser.Lexer.d_isDotHead_436
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0)))
      else coe
             du_it'45'dot_102 (coe v0) (coe v0) (coe v1) (coe v3)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isDotHead_436 (coe v0))
-- Once.Format.Lex.it-eqop
d_it'45'eqop_118 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 -> Bool -> [T_Item_6]
d_it'45'eqop_118 v0 v1 ~v2 v3 v4 v5
  = du_it'45'eqop_118 v0 v1 v3 v4 v5
du_it'45'eqop_118 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 -> Bool -> [T_Item_6]
du_it'45'eqop_118 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_it'45'dot_102 (coe v0)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0)) (coe v1)
             (coe v2)
             (coe
                MAlonzo.Code.Once.Parser.Lexer.d_isDotHead_436
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0)))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_tok_8 (coe v3))
             (coe
                du_items'45'WF_34 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Format.Lex.it-lbrace
d_it'45'lbrace_126 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> [T_Item_6]
d_it'45'lbrace_126 v0 v1 ~v2 v3 = du_it'45'lbrace_126 v0 v1 v3
du_it'45'lbrace_126 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> [T_Item_6]
du_it'45'lbrace_126 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                C_comment_10
                (coe
                   MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '{')
                      (coe
                         d_consumed_24 (coe v0)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Parser.Lexer.d_skipBlockB_388
                               (coe (1 :: Integer))
                               (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))))))))
             (coe
                du_items'45'WF_34
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_skipBlockB_388
                      (coe (1 :: Integer))
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_skipBlockB_388
                         (coe (1 :: Integer))
                         (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))))
                   (coe v1)))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TLBrace_20))
             (coe
                du_items'45'WF_34 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Format.Lex.it-minus
d_it'45'minus_134 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Parser.Lexer.T_Dash3_410 -> [T_Item_6]
d_it'45'minus_134 v0 v1 ~v2 v3 = du_it'45'minus_134 v0 v1 v3
du_it'45'minus_134 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> MAlonzo.Code.Once.Parser.Lexer.T_Dash3_410 -> [T_Item_6]
du_it'45'minus_134 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'comment_412
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                C_comment_10
                (coe
                   MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '-')
                      (coe
                         d_consumed_24 (coe v0)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Parser.Lexer.d_skipLineB_274
                               (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))))))))
             (coe
                du_items'45'WF_34
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_skipLineB_274
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_skipLineB_274
                         (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'arrow_414
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28))
             (coe
                du_items'45'WF_34
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'minus_416
        -> coe
             du_it'45'dot_102 (coe v0) (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'45'_12)
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isDotHead_436 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Lex.it-caret
d_it'45'caret_142 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_418 -> [T_Item_6]
d_it'45'caret_142 v0 v1 ~v2 v3 = du_it'45'caret_142 v0 v1 v3
du_it'45'caret_142 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_418 -> [T_Item_6]
du_it'45'caret_142 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'1_420
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TCaret1_30))
             (coe
                du_items'45'WF_34
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'0_422
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TCaret0_32))
             (coe
                du_items'45'WF_34
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'w_424
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_tok_8 (coe MAlonzo.Code.Once.Parser.Token.C_TCaretW_34))
             (coe
                du_items'45'WF_34
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_634 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_452 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'gen_426
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Lex.lexItems
d_lexItems_580 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> [T_Item_6]
d_lexItems_580 v0
  = coe du_items'45'WF_34 (coe v0) (coe (0 :: Integer))
-- Once.Format.Lex.tokens-WF
d_tokens'45'WF_590 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'WF_590 = erased
-- Once.Format.Lex.tokens-head
d_tokens'45'head_604 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Parser.Lexer.T_HeadK_462 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'head_604 = erased
-- Once.Format.Lex.tokens-str
d_tokens'45'str_616 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'str_616 = erased
-- Once.Format.Lex.tokens-gen
d_tokens'45'gen_632 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'gen_632 = erased
-- Once.Format.Lex.tokens-num
d_tokens'45'num_652 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'num_652 = erased
-- Once.Format.Lex.tokens-nl
d_tokens'45'nl_664 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'nl_664 = erased
-- Once.Format.Lex.tokens-dot
d_tokens'45'dot_682 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'dot_682 = erased
-- Once.Format.Lex.tokens-cmp
d_tokens'45'cmp_698 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'cmp_698 = erased
-- Once.Format.Lex.tokens-eqop
d_tokens'45'eqop_714 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'eqop_714 = erased
-- Once.Format.Lex.tokens-lbrace
d_tokens'45'lbrace_726 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'lbrace_726 = erased
-- Once.Format.Lex.tokens-minus
d_tokens'45'minus_738 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Parser.Lexer.T_Dash3_410 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'minus_738 = erased
-- Once.Format.Lex.tokens-caret
d_tokens'45'caret_750 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'caret_750 = erased
-- Once.Format.Lex.tokens-lexItems
d_tokens'45'lexItems_1228 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tokens'45'lexItems_1228 = erased
