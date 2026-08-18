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

module MAlonzo.Code.Once.Parser.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Core.Parser
d_Parser_6 :: () -> ()
d_Parser_6 = erased
-- Once.Parser.Core.return
d_return_12 ::
  () ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_return_12 ~v0 v1 v2 = du_return_12 v1 v2
du_return_12 ::
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_return_12 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
-- Once.Parser.Core._>>=_
d__'62''62''61'__22 ::
  () ->
  () ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'62''62''61'__22 ~v0 ~v1 v2 v3 v4
  = du__'62''62''61'__22 v2 v3 v4
du__'62''62''61'__22 ::
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'62''62''61'__22 v0 v1 v2
  = let v3 = coe v0 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v1 v5 v6
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Core._>>_
d__'62''62'__54 ::
  () ->
  () ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'62''62'__54 ~v0 ~v1 v2 v3 = du__'62''62'__54 v2 v3
du__'62''62'__54 ::
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'62''62'__54 v0 v1
  = coe du__'62''62''61'__22 (coe v0) (coe (\ v2 -> v1))
-- Once.Parser.Core._<$>_
d__'60''36''62'__66 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'60''36''62'__66 ~v0 ~v1 v2 v3 v4
  = du__'60''36''62'__66 v2 v3 v4
du__'60''36''62'__66 ::
  (AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'60''36''62'__66 v0 v1 v2
  = let v3 = coe v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v5) (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Core.fail
d_fail_96 ::
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fail_96 ~v0 ~v1 = du_fail_96
du_fail_96 :: Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fail_96 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Parser.Core._<|>_
d__'60''124''62'__100 ::
  () ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'60''124''62'__100 ~v0 v1 v2 v3
  = du__'60''124''62'__100 v1 v2 v3
du__'60''124''62'__100 ::
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'60''124''62'__100 v0 v1 v2
  = let v3 = coe v0 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Core.satisfy
d_satisfy_128 ::
  () ->
  (MAlonzo.Code.Once.Parser.Token.T_Token_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfy_128 ~v0 v1 v2 = du_satisfy_128 v1 v2
du_satisfy_128 ::
  (MAlonzo.Code.Once.Parser.Token.T_Token_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfy_128 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> let v4 = coe v0 v2 in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Core.peek
d_peek_156 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peek_156 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v0))
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)) (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Core.expect
d_expect_162 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_expect_162 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3 -> coe du_matchToken_174 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Core._.matchToken
d_matchToken_174 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_matchToken_174 ~v0 ~v1 ~v2 v3 v4 v5 = du_matchToken_174 v3 v4 v5
du_matchToken_174 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_matchToken_174 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Parser.Token.C_TLParen_16
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TRParen_18
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TColon_24
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TColon_24
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TEquals_26
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TEquals_26
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TArrow_28
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TLambda_36
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TLambda_36
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TComma_38
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TComma_38
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TAt_42
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TAt_42
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TPipe_44
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TPipe_44
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TDot_46
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TDot_46
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TPlus_48
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TPlus_48
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TMinus_50
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TMinus_50
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TStar_52
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TStar_52
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TSlash_54
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TSlash_54
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TPercent_56
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TPercent_56
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TLt_60
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TLt_60
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TLe_62
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TLe_62
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TGt_64
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TGt_64
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TGe_66
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TGe_66
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TNeq_70
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TNeq_70
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TNewline_74
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TNewline_74
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         MAlonzo.Code.Once.Parser.Token.C_TEOF_76
           -> case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TEOF_76
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                _ -> coe v3
         _ -> coe v3)
-- Once.Parser.Core.word
d_word_228 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_word_228 v0 = coe du_satisfy_128 (coe d_check_236 (coe v0))
-- Once.Parser.Core._.check
d_check_236 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_check_236 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Parser.Token.C_TWord_8 v3
           -> let v4
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v4 ->
                           coe
                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                             (coe v0))
                        (coe
                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                           (coe v3)) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                     -> if coe v5
                          then coe
                                 seq (coe v6)
                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0))
                          else coe
                                 seq (coe v6) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v2)
-- Once.Parser.Core.anyWord
d_anyWord_248 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_anyWord_248
  = coe
      du_satisfy_128
      (coe
         (\ v0 ->
            let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
            coe
              (case coe v0 of
                 MAlonzo.Code.Once.Parser.Token.C_TWord_8 v2
                   -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                 _ -> coe v1)))
-- Once.Parser.Core.optional
d_optional_256 ::
  () ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_optional_256 ~v0 v1 v2 = du_optional_256 v1 v2
du_optional_256 ::
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_optional_256 v0 v1
  = let v2 = coe v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v1))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Core.skipNewlines
d_skipNewlines_278 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipNewlines_278 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v0))
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TNewline_74
                  -> let v4 = d_skipNewlines_278 (coe v2) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                                              (coe v6))
                                           (coe v7))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                    (coe v2))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
