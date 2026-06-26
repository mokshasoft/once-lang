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

module MAlonzo.Code.Once.Parser where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Parser.TypeAlias
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.parse
d_parse_4 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44
d_parse_4 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (let v1
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634 (coe v0) in
                  coe
                    (let v2
                           = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634 (coe v0)) in
                     coe
                       (case coe v2 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                            -> case coe v3 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                                   -> let v6
                                            = MAlonzo.Code.Once.Parser.Module.d_parseDeclB_8
                                                (coe v5) in
                                      coe
                                        (let v7
                                               = coe
                                                   MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_174
                                                   (coe v1) in
                                         coe
                                           (case coe v6 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                -> case coe v8 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                       -> case coe v10 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                              -> let v13
                                                                       = coe
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_284
                                                                           (coe v11) in
                                                                 coe
                                                                   (case coe v13 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe v9)
                                                                                       (coe v14))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v16)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                          (coe v17)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                (coe
                                                                                                   v12))
                                                                                             (coe
                                                                                                v7))))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v5) (coe v7))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (coe (\ v3 v4 -> addInt (coe (1 :: Integer)) (coe v4)))
                                          (coe (0 :: Integer)) (coe v1))))
                          _ -> MAlonzo.RTE.mazUnreachableError)))) in
    coe (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
-- Once.Parser.allTrailing
d_allTrailing_18 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> Bool
d_allTrailing_18 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TNewline_72
                  -> coe d_allTrailing_18 (coe v3)
                MAlonzo.Code.Once.Parser.Token.C_TEOF_74
                  -> coe d_allTrailing_18 (coe v3)
                _ -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.showTokenPrefix
d_showTokenPrefix_24 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showTokenPrefix_24 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Parser.Token.C_TWord_8 v3
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("TWord \"" :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                       ("\"" :: Data.Text.Text))
             MAlonzo.Code.Once.Parser.Token.C_TInt_10 v3
               -> coe ("TInt" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TString_12 v3
               -> coe ("TString" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TLParen_14
               -> coe ("TLParen" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TRParen_16
               -> coe ("TRParen" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TLBrace_18
               -> coe ("TLBrace" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TRBrace_20
               -> coe ("TRBrace" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TColon_22
               -> coe ("TColon" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TEquals_24
               -> coe ("TEquals" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TArrow_26
               -> coe ("TArrow" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TCaret1_28
               -> coe ("TCaret1" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TCaret0_30
               -> coe ("TCaret0" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TCaretW_32
               -> coe ("TCaretW" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TLambda_34
               -> coe ("TLambda" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TComma_36
               -> coe ("TComma" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TSemicolon_38
               -> coe ("TSemicolon" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TAt_40
               -> coe ("TAt" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TPipe_42
               -> coe ("TPipe" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TDot_44
               -> coe ("TDot" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TPlus_46
               -> coe ("TPlus" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TMinus_48
               -> coe ("TMinus" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TStar_50
               -> coe ("TStar" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TSlash_52
               -> coe ("TSlash" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TPercent_54
               -> coe ("TPercent" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TAmpersand_56
               -> coe ("TAmpersand" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TLt_58
               -> coe ("TLt" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TLe_60
               -> coe ("TLe" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TGt_62
               -> coe ("TGt" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TGe_64
               -> coe ("TGe" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TEqEq_66
               -> coe ("TEqEq" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TNeq_68
               -> coe ("TNeq" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TBang_70
               -> coe ("TBang" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TNewline_72
               -> coe d_showTokenPrefix_24 (coe v2)
             MAlonzo.Code.Once.Parser.Token.C_TEOF_74
               -> coe d_showTokenPrefix_24 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.parseStrict
d_parseStrict_32 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseStrict_32 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (let v1
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634 (coe v0) in
                  coe
                    (let v2
                           = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634 (coe v0)) in
                     coe
                       (case coe v2 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                            -> case coe v3 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                                   -> let v6
                                            = MAlonzo.Code.Once.Parser.Module.d_parseDeclB_8
                                                (coe v5) in
                                      coe
                                        (let v7
                                               = coe
                                                   MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_174
                                                   (coe v1) in
                                         coe
                                           (case coe v6 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                -> case coe v8 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                       -> case coe v10 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                              -> let v13
                                                                       = coe
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_284
                                                                           (coe v11) in
                                                                 coe
                                                                   (case coe v13 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe v9)
                                                                                       (coe v14))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v16)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                          (coe v17)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                (coe
                                                                                                   v12))
                                                                                             (coe
                                                                                                v7))))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v5) (coe v7))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (coe (\ v3 v4 -> addInt (coe (1 :: Integer)) (coe v4)))
                                          (coe (0 :: Integer)) (coe v1))))
                          _ -> MAlonzo.RTE.mazUnreachableError)))) in
    coe
      (let v2
             = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (let v2
                           = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634 (coe v0) in
                     coe
                       (let v3
                              = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                  (coe
                                     MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634
                                     (coe v0)) in
                        coe
                          (case coe v3 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                               -> case coe v4 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                      -> let v7
                                               = MAlonzo.Code.Once.Parser.Module.d_parseDeclB_8
                                                   (coe v6) in
                                         coe
                                           (let v8
                                                  = coe
                                                      MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_174
                                                      (coe v2) in
                                            coe
                                              (case coe v7 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                                   -> case coe v9 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                          -> case coe v11 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                 -> let v14
                                                                          = coe
                                                                              MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_284
                                                                              (coe v12) in
                                                                    coe
                                                                      (case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                           -> case coe v16 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                  -> coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe v10)
                                                                                          (coe v15))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe v17)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                             (coe
                                                                                                v18)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                   (coe
                                                                                                      v13))
                                                                                                (coe
                                                                                                   v8))))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v6) (coe v8))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du_foldr_216
                                             (coe (\ v4 v5 -> addInt (coe (1 :: Integer)) (coe v5)))
                                             (coe (0 :: Integer)) (coe v2))))
                             _ -> MAlonzo.RTE.mazUnreachableError)))) in
       coe
         (let v3 = d_allTrailing_18 (coe v2) in
          coe
            (if coe v3
               then coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v1)
               else coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("Parse error: unexpected tokens remaining after last parsed decl (starting at: "
                          ::
                          Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_showTokenPrefix_24 (coe v2))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (")" :: Data.Text.Text) (coe du_tvarHint_80 (coe v2))))))))
-- Once.Parser._.knownType
d_knownType_68 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_knownType_68 ~v0 ~v1 ~v2 v3 = du_knownType_68 v3
du_knownType_68 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
du_knownType_68 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
         (coe
            MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
            (coe ("Unit" :: Data.Text.Text))))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
            (coe
               MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
               (coe ("Void" :: Data.Text.Text))))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe
               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
               (coe
                  MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                  (coe ("Int" :: Data.Text.Text))))
            (coe
               MAlonzo.Code.Data.Bool.Base.d__'8744'__30
               (coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                  (coe
                     MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                     (coe ("Float" :: Data.Text.Text))))
               (coe
                  MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                  (coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                        (coe ("Buffer" :: Data.Text.Text))))
                  (coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                        (coe ("String" :: Data.Text.Text))))))))
-- Once.Parser._.hasUpperTVar
d_hasUpperTVar_72 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> Bool
d_hasUpperTVar_72 ~v0 ~v1 ~v2 v3 = du_hasUpperTVar_72 v3
du_hasUpperTVar_72 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> Bool
du_hasUpperTVar_72 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3 = coe du_hasUpperTVar_72 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe MAlonzo.Code.Once.Parser.Type.d_isUpperWord_6 (coe v4))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d_not_22
                             (coe du_knownType_68 (coe v4))))
                       (coe du_hasUpperTVar_72 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.tvarHint
d_tvarHint_80 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_tvarHint_80 ~v0 ~v1 ~v2 v3 = du_tvarHint_80 v3
du_tvarHint_80 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_tvarHint_80 v0
  = let v1 = coe du_hasUpperTVar_72 (coe v0) in
    coe
      (if coe v1
         then coe
                ("\n  hint: type variables must be lowercase (e.g. `a`, not `A`); uppercase names like `Int`/`Unit` are concrete types"
                 ::
                 Data.Text.Text)
         else coe ("" :: Data.Text.Text))
-- Once.Parser.extractAliases
d_extractAliases_92 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extractAliases_92 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v1
        -> coe du_go_100 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.go
d_go_100 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go_100 ~v0 v1 = du_go_100 v1
du_go_100 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go_100 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = coe du_go_100 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6)))
                       (coe du_go_100 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo
d_FunInfo_112 = ()
data T_FunInfo_112
  = C_mkFunInfo_134 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    (Maybe MAlonzo.Code.Once.Type.T_Type_112)
                    (Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8)
                    MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 Bool
-- Once.Parser.FunInfo.funName
d_funName_124 ::
  T_FunInfo_112 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_funName_124 v0
  = case coe v0 of
      C_mkFunInfo_134 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funType
d_funType_126 ::
  T_FunInfo_112 -> Maybe MAlonzo.Code.Once.Type.T_Type_112
d_funType_126 v0
  = case coe v0 of
      C_mkFunInfo_134 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funAlloc
d_funAlloc_128 ::
  T_FunInfo_112 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8
d_funAlloc_128 v0
  = case coe v0 of
      C_mkFunInfo_134 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funBody
d_funBody_130 ::
  T_FunInfo_112 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_funBody_130 v0
  = case coe v0 of
      C_mkFunInfo_134 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funIsPrimitive
d_funIsPrimitive_132 :: T_FunInfo_112 -> Bool
d_funIsPrimitive_132 v0
  = case coe v0 of
      C_mkFunInfo_134 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo
d_PolyFunInfo_136 = ()
data T_PolyFunInfo_136
  = C_mkPolyFunInfo_154 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Type.T_PolyType_244
                        (Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8)
                        MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
-- Once.Parser.PolyFunInfo.pfunName
d_pfunName_146 ::
  T_PolyFunInfo_136 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_pfunName_146 v0
  = case coe v0 of
      C_mkPolyFunInfo_154 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunType
d_pfunType_148 ::
  T_PolyFunInfo_136 -> MAlonzo.Code.Once.Type.T_PolyType_244
d_pfunType_148 v0
  = case coe v0 of
      C_mkPolyFunInfo_154 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunAlloc
d_pfunAlloc_150 ::
  T_PolyFunInfo_136 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8
d_pfunAlloc_150 v0
  = case coe v0 of
      C_mkPolyFunInfo_154 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunBody
d_pfunBody_152 ::
  T_PolyFunInfo_136 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_pfunBody_152 v0
  = case coe v0 of
      C_mkPolyFunInfo_154 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.projectSig
d_projectSig_156 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_projectSig_156 v0 v1 v2
  = let v3 = MAlonzo.Code.Once.Type.d_isGround_436 (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48 (coe v0)
                   (coe MAlonzo.Code.Once.Type.d_extractGround_320 (coe v2) (coe v4)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Polymorphic signature not admissible here for `"
                    ::
                    Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("`: " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (MAlonzo.Code.Once.Type.d_showPolyType_468 (coe v2))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (" \8212 primitives and type aliases must be ground. "
                                ::
                                Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("User `DFunDef`s with polymorphic sigs route into "
                                   ::
                                   Data.Text.Text)
                                  ("`PolyFunInfo` (plan 0.6 Phase C.1)." :: Data.Text.Text)))))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.PendingSig
d_PendingSig_182 :: ()
d_PendingSig_182 = erased
-- Once.Parser.EFResult
d_EFResult_184 :: ()
d_EFResult_184 = erased
-- Once.Parser.extractFunctions-consFun
d_extractFunctions'45'consFun_186 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_FunInfo_112 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions'45'consFun_186 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v3))
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.extractFunctions-consPoly
d_extractFunctions'45'consPoly_196 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_PolyFunInfo_136 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions'45'consPoly_196 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.extractFunctions-go
d_extractFunctions'45'go_206 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions'45'go_206 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v1))
      (:) v3 v4
        -> let v5
                 = d_extractFunctions'45'go_206 (coe v0) (coe v4) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 v6 v7
                  -> let v8 = MAlonzo.Code.Once.Type.d_isGround_436 (coe v7) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                            -> coe
                                 d_extractFunctions'45'go_206 (coe v0) (coe v4)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                          (coe
                                             MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48
                                             (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.Type.d_extractGround_320 (coe v7)
                                                (coe v9))))))
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                            -> coe
                                 d_extractFunctions'45'go_206 (coe v0) (coe v4)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v7))))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 v6 v7 v8
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                         -> case coe v9 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> case coe v11 of
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                       -> let v13
                                                = coe
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                    erased
                                                    (\ v13 ->
                                                       coe
                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                         (coe v10))
                                                    (coe
                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                       (coe v10) (coe v6)) in
                                          coe
                                            (case coe v13 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                 -> if coe v14
                                                      then coe
                                                             seq (coe v15)
                                                             (coe
                                                                d_extractFunctions'45'consFun_186
                                                                (coe
                                                                   d_extractFunctions'45'go_206
                                                                   (coe v0) (coe v4)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                                                (coe
                                                                   C_mkFunInfo_134 (coe v6)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                      (coe v12))
                                                                   (coe v7) (coe v8)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                d_extractFunctions'45'go_206
                                                                (coe v0) (coe v4)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                       -> let v13
                                                = coe
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                    erased
                                                    (\ v13 ->
                                                       coe
                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                         (coe v10))
                                                    (coe
                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                       (coe v10) (coe v6)) in
                                          coe
                                            (case coe v13 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                 -> if coe v14
                                                      then coe
                                                             seq (coe v15)
                                                             (coe
                                                                d_extractFunctions'45'consPoly_196
                                                                (coe
                                                                   d_extractFunctions'45'go_206
                                                                   (coe v0) (coe v4)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                                                (coe
                                                                   C_mkPolyFunInfo_154 (coe v6)
                                                                   (coe v12) (coe v7) (coe v8)))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                d_extractFunctions'45'go_206
                                                                (coe v0) (coe v4)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              d_extractFunctions'45'consFun_186
                              (coe d_extractFunctions'45'go_206 (coe v0) (coe v4) (coe v2))
                              (coe
                                 C_mkFunInfo_134 (coe v6) (coe v2) (coe v7) (coe v8)
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v6 v7 v8 v9
                  -> case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                         -> let v11 = MAlonzo.Code.Once.Type.d_isGround_436 (coe v8) in
                            coe
                              (let v12
                                     = coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v10
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            ("." :: Data.Text.Text) v6) in
                               coe
                                 (case coe v11 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                      -> let v14
                                               = MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48
                                                   (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.d_extractGround_320
                                                      (coe v8) (coe v13)) in
                                         coe
                                           (coe
                                              d_extractFunctions'45'consFun_186
                                              (coe
                                                 d_extractFunctions'45'go_206 (coe v0) (coe v4)
                                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                              (coe
                                                 C_mkFunInfo_134
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    v10
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       ("." :: Data.Text.Text) v6))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                    (coe v14))
                                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       v10
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          ("." :: Data.Text.Text) v6)))
                                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)))
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                      -> coe
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("Polymorphic signature not admissible here for `"
                                               ::
                                               Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v12
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("`: " :: Data.Text.Text)
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       (MAlonzo.Code.Once.Type.d_showPolyType_468
                                                          (coe v8))
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          (" \8212 primitives and type aliases must be ground. "
                                                           ::
                                                           Data.Text.Text)
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             ("User `DFunDef`s with polymorphic sigs route into "
                                                              ::
                                                              Data.Text.Text)
                                                             ("`PolyFunInfo` (plan 0.6 Phase C.1)."
                                                              ::
                                                              Data.Text.Text)))))))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> let v10 = MAlonzo.Code.Once.Type.d_isGround_436 (coe v8) in
                            coe
                              (case coe v10 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                   -> let v12
                                            = MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48
                                                (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.Type.d_extractGround_320
                                                   (coe v8) (coe v11)) in
                                      coe
                                        (coe
                                           d_extractFunctions'45'consFun_186
                                           (coe
                                              d_extractFunctions'45'go_206 (coe v0) (coe v4)
                                              (coe v7))
                                           (coe
                                              C_mkFunInfo_134 (coe v6)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                 (coe v12))
                                              (coe v7)
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 (coe v6))
                                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)))
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("Polymorphic signature not admissible here for `"
                                            ::
                                            Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20 v6
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 ("`: " :: Data.Text.Text)
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    (MAlonzo.Code.Once.Type.d_showPolyType_468
                                                       (coe v8))
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       (" \8212 primitives and type aliases must be ground. "
                                                        ::
                                                        Data.Text.Text)
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          ("User `DFunDef`s with polymorphic sigs route into "
                                                           ::
                                                           Data.Text.Text)
                                                          ("`PolyFunInfo` (plan 0.6 Phase C.1)."
                                                           ::
                                                           Data.Text.Text)))))))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.nameElem
d_nameElem_420 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_nameElem_420 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v2 v3
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
                        (coe v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe v5)
                       else coe seq (coe v6) (coe d_nameElem_420 (coe v0) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.namesDistinct
d_namesDistinct_444 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_namesDistinct_444 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe
                MAlonzo.Code.Data.Bool.Base.d_not_22
                (coe d_nameElem_420 (coe v1) (coe v2)))
             (coe d_namesDistinct_444 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.allIdentContinue
d_allIdentContinue_450 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_allIdentContinue_450 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentContinue_12 (coe v1))
             (coe d_allIdentContinue_450 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.validCharsB
d_validCharsB_456 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_validCharsB_456 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentStart_8 (coe v1))
             (coe d_allIdentContinue_450 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.validIdentB
d_validIdentB_462 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_validIdentB_462 v0
  = coe
      d_validCharsB_456
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Parser.allValidIdentB
d_allValidIdentB_466 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_allValidIdentB_466 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_validIdentB_462 (coe v1))
             (coe d_allValidIdentB_466 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.emittedNames-cons
d_emittedNames'45'cons_472 ::
  Bool ->
  T_FunInfo_112 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedNames'45'cons_472 v0 v1 v2
  = if coe v0
      then coe v2
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_funName_124 (coe v1)) (coe v2)
-- Once.Parser.emittedNames
d_emittedNames_482 ::
  [T_FunInfo_112] -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedNames_482 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             d_emittedNames'45'cons_472 (coe d_funIsPrimitive_132 (coe v1))
             (coe v1) (coe d_emittedNames_482 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.distinctOrErr
d_distinctOrErr_488 ::
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_distinctOrErr_488 v0 v1
  = if coe v0
      then coe v1
      else coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                ("ill-formed top-level definition name (duplicate or not an identifier)"
                 ::
                 Data.Text.Text))
-- Once.Parser.guardDistinct
d_guardDistinct_492 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_guardDistinct_492 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe
                    d_distinctOrErr_488
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_namesDistinct_444 (coe du_nms_504 (coe v2)))
                       (coe d_allValidIdentB_466 (coe du_nms_504 (coe v2))))
                    (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.nms
d_nms_504 ::
  [T_FunInfo_112] ->
  [T_PolyFunInfo_136] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_nms_504 v0 ~v1 = du_nms_504 v0
du_nms_504 ::
  [T_FunInfo_112] -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_nms_504 v0 = coe d_emittedNames_482 (coe v0)
-- Once.Parser.extractFunctions
d_extractFunctions_506 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions_506 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v2
        -> coe
             d_guardDistinct_492
             (coe
                d_extractFunctions'45'go_206 (coe v0) (coe v2)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
