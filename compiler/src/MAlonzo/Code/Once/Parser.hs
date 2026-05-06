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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
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
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v0) in
                  coe
                    (let v2
                           = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v0)) in
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
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_282
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
                MAlonzo.Code.Once.Parser.Token.C_TNewline_70
                  -> coe d_allTrailing_18 (coe v3)
                MAlonzo.Code.Once.Parser.Token.C_TEOF_72
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
             MAlonzo.Code.Once.Parser.Token.C_TNewline_70
               -> coe d_showTokenPrefix_24 (coe v2)
             MAlonzo.Code.Once.Parser.Token.C_TEOF_72
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
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v0) in
                  coe
                    (let v2
                           = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v0)) in
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
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_282
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
                           = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v0) in
                     coe
                       (let v3
                              = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                  (coe
                                     MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630
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
                                                                              MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_282
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
                            (d_showTokenPrefix_24 (coe v2)) (")" :: Data.Text.Text))))))
-- Once.Parser.extractAliases
d_extractAliases_64 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extractAliases_64 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v1
        -> coe du_go_72 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.go
d_go_72 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go_72 ~v0 v1 = du_go_72 v1
du_go_72 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go_72 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = coe du_go_72 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6)))
                       (coe du_go_72 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo
d_FunInfo_84 = ()
data T_FunInfo_84
  = C_mkFunInfo_106 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Once.Type.T_Type_108
                    (Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8)
                    MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 Bool
-- Once.Parser.FunInfo.funName
d_funName_96 ::
  T_FunInfo_84 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_funName_96 v0
  = case coe v0 of
      C_mkFunInfo_106 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funType
d_funType_98 :: T_FunInfo_84 -> MAlonzo.Code.Once.Type.T_Type_108
d_funType_98 v0
  = case coe v0 of
      C_mkFunInfo_106 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funAlloc
d_funAlloc_100 ::
  T_FunInfo_84 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8
d_funAlloc_100 v0
  = case coe v0 of
      C_mkFunInfo_106 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funBody
d_funBody_102 ::
  T_FunInfo_84 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_funBody_102 v0
  = case coe v0 of
      C_mkFunInfo_106 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funIsPrimitive
d_funIsPrimitive_104 :: T_FunInfo_84 -> Bool
d_funIsPrimitive_104 v0
  = case coe v0 of
      C_mkFunInfo_106 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo
d_PolyFunInfo_108 = ()
data T_PolyFunInfo_108
  = C_mkPolyFunInfo_126 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Type.T_PolyType_240
                        (Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8)
                        MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
-- Once.Parser.PolyFunInfo.pfunName
d_pfunName_118 ::
  T_PolyFunInfo_108 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_pfunName_118 v0
  = case coe v0 of
      C_mkPolyFunInfo_126 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunType
d_pfunType_120 ::
  T_PolyFunInfo_108 -> MAlonzo.Code.Once.Type.T_PolyType_240
d_pfunType_120 v0
  = case coe v0 of
      C_mkPolyFunInfo_126 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunAlloc
d_pfunAlloc_122 ::
  T_PolyFunInfo_108 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8
d_pfunAlloc_122 v0
  = case coe v0 of
      C_mkPolyFunInfo_126 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunBody
d_pfunBody_124 ::
  T_PolyFunInfo_108 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_pfunBody_124 v0
  = case coe v0 of
      C_mkPolyFunInfo_126 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.projectSig
d_projectSig_128 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_projectSig_128 v0 v1 v2
  = let v3 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48 (coe v0)
                   (coe MAlonzo.Code.Once.Type.d_extractGround_316 (coe v2) (coe v4)))
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
                            (MAlonzo.Code.Once.Type.d_showPolyType_464 (coe v2))
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
d_PendingSig_154 :: ()
d_PendingSig_154 = erased
-- Once.Parser.extractFunctions
d_extractFunctions_156 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions_156 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v2
        -> coe
             du_go_188 (coe v0) (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.Result
d_Result_166 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] -> ()
d_Result_166 = erased
-- Once.Parser._.consFun
d_consFun_168 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_FunInfo_84 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_consFun_168 ~v0 ~v1 v2 v3 = du_consFun_168 v2 v3
du_consFun_168 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_FunInfo_84 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_consFun_168 v0 v1
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
-- Once.Parser._.consPoly
d_consPoly_178 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_PolyFunInfo_108 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_consPoly_178 ~v0 ~v1 v2 v3 = du_consPoly_178 v2 v3
du_consPoly_178 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_PolyFunInfo_108 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_consPoly_178 v0 v1
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
-- Once.Parser._.go
d_go_188 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_go_188 v0 ~v1 v2 v3 = du_go_188 v0 v2 v3
du_go_188 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_go_188 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v1))
      (:) v3 v4
        -> let v5 = coe du_go_188 (coe v0) (coe v4) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 v6 v7
                  -> let v8 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v7) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                            -> coe
                                 du_go_188 (coe v0) (coe v4)
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
                                                MAlonzo.Code.Once.Type.d_extractGround_316 (coe v7)
                                                (coe v9))))))
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                            -> coe
                                 du_go_188 (coe v0) (coe v4)
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
                                                                du_consFun_168
                                                                (coe
                                                                   du_go_188 (coe v0) (coe v4)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                                                (coe
                                                                   C_mkFunInfo_106 (coe v6)
                                                                   (coe v12) (coe v7) (coe v8)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                du_go_188 (coe v0) (coe v4)
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
                                                                du_consPoly_178
                                                                (coe
                                                                   du_go_188 (coe v0) (coe v4)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                                                (coe
                                                                   C_mkPolyFunInfo_126 (coe v6)
                                                                   (coe v12) (coe v7) (coe v8)))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                du_go_188 (coe v0) (coe v4)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe du_go_188 (coe v0) (coe v4) (coe v2)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v6 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                         -> let v10 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v8) in
                            coe
                              (let v11
                                     = coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v9
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            ("." :: Data.Text.Text) v6) in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                      -> let v13
                                               = MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48
                                                   (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.d_extractGround_316
                                                      (coe v8) (coe v12)) in
                                         coe
                                           (coe
                                              du_consFun_168
                                              (coe
                                                 du_go_188 (coe v0) (coe v4)
                                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                              (coe
                                                 C_mkFunInfo_106
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v9
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       ("." :: Data.Text.Text) v6))
                                                 (coe v13)
                                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       v9
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          ("." :: Data.Text.Text) v6)))
                                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)))
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                      -> coe
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("Polymorphic signature not admissible here for `"
                                               ::
                                               Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v11
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("`: " :: Data.Text.Text)
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       (MAlonzo.Code.Once.Type.d_showPolyType_464
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
                         -> let v9 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v8) in
                            coe
                              (case coe v9 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                   -> let v11
                                            = MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48
                                                (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.Type.d_extractGround_316
                                                   (coe v8) (coe v10)) in
                                      coe
                                        (coe
                                           du_consFun_168 (coe du_go_188 (coe v0) (coe v4) (coe v7))
                                           (coe
                                              C_mkFunInfo_106 (coe v6) (coe v11) (coe v7)
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 (coe v6))
                                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)))
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
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
                                                    (MAlonzo.Code.Once.Type.d_showPolyType_464
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
