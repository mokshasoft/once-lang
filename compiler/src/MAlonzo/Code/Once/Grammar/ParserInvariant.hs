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

module MAlonzo.Code.Once.Grammar.ParserInvariant where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Once.Grammar.Convert
import qualified MAlonzo.Code.Once.Grammar.ParserBridge
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Type

-- Once.Grammar.ParserInvariant.ParsesAtom-NoMuNu
d_ParsesAtom'45'NoMuNu_12 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
d_ParsesAtom'45'NoMuNu_12 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'unit_112
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'unit_514
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'void_116
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'void_516
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'int_120
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'int_518
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'float_124
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'float_520
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'buffer_128
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'buffer_524
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'string_132
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'str_522
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'eff_144 v5 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'eff_550
                           (d_ParsesAtom'45'NoMuNu_12 (coe v12) (coe v13) (coe v5) (coe v9))
                           (d_ParsesAtom'45'NoMuNu_12 (coe v5) (coe v15) (coe v2) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'io_152 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'eff_550
                           (coe MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'unit_514)
                           (d_ParsesAtom'45'NoMuNu_12 (coe v9) (coe v12) (coe v2) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_162 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    d_ParsesType'45'NoMuNu_66 (coe v11) (coe v1)
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_16) (coe v2))
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesProd-NoMuNu
d_ParsesProd'45'NoMuNu_20 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProd_98 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
d_ParsesProd'45'NoMuNu_20 v0 ~v1 ~v2 v3
  = du_ParsesProd'45'NoMuNu_20 v0 v3
du_ParsesProd'45'NoMuNu_20 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProd_98 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
du_ParsesProd'45'NoMuNu_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_174 v3 v5 v7 v8
        -> coe
             du_ParsesProdTail'45'NoMuNu_30 (coe v3) (coe v8)
             (coe d_ParsesAtom'45'NoMuNu_12 (coe v0) (coe v5) (coe v3) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesProdTail-NoMuNu
d_ParsesProdTail'45'NoMuNu_30 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProdTail_100 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
d_ParsesProdTail'45'NoMuNu_30 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ParsesProdTail'45'NoMuNu_30 v1 v4 v5
du_ParsesProdTail'45'NoMuNu_30 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProdTail_100 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
du_ParsesProdTail'45'NoMuNu_30 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_180 v5
        -> coe v2
      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'star_194 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    du_ParsesProdTail'45'NoMuNu_30 (coe v5) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'prod_530 v2
                       (d_ParsesAtom'45'NoMuNu_12 (coe v12) (coe v7) (coe v5) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesSum-NoMuNu
d_ParsesSum'45'NoMuNu_38 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSum_102 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
d_ParsesSum'45'NoMuNu_38 v0 ~v1 ~v2 v3
  = du_ParsesSum'45'NoMuNu_38 v0 v3
du_ParsesSum'45'NoMuNu_38 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSum_102 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
du_ParsesSum'45'NoMuNu_38 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206 v3 v5 v7 v8
        -> coe
             du_ParsesSumTail'45'NoMuNu_48 (coe v3) (coe v8)
             (coe du_ParsesProd'45'NoMuNu_20 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesSumTail-NoMuNu
d_ParsesSumTail'45'NoMuNu_48 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSumTail_104 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
d_ParsesSumTail'45'NoMuNu_48 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ParsesSumTail'45'NoMuNu_48 v1 v4 v5
du_ParsesSumTail'45'NoMuNu_48 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSumTail_104 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
du_ParsesSumTail'45'NoMuNu_48 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_212 v5
        -> coe v2
      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'plus_226 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    du_ParsesSumTail'45'NoMuNu_48 (coe v5) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'sum_536 v2
                       (coe du_ParsesProd'45'NoMuNu_20 (coe v12) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesArrowTail-NoMuNu
d_ParsesArrowTail'45'NoMuNu_58 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesArrowTail_108 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
d_ParsesArrowTail'45'NoMuNu_58 ~v0 v1 v2 v3 v4 v5
  = du_ParsesArrowTail'45'NoMuNu_58 v1 v2 v3 v4 v5
du_ParsesArrowTail'45'NoMuNu_58 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesArrowTail_108 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
du_ParsesArrowTail'45'NoMuNu_58 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_244 v7
        -> coe v4
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_256 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v12 of
                    (:) v13 v14
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'fun_544 v4
                                  (d_ParsesType'45'NoMuNu_66 (coe v14) (coe v17) (coe v2) (coe v10))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow_266 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_nmn'45'fun_544 v4
                           (d_ParsesType'45'NoMuNu_66 (coe v11) (coe v14) (coe v2) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesType-NoMuNu
d_ParsesType'45'NoMuNu_66 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
d_ParsesType'45'NoMuNu_66 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238 v5 v7 v9 v10
        -> coe
             du_ParsesArrowTail'45'NoMuNu_58 (coe v5) (coe v1) (coe v2)
             (coe v10) (coe du_ParsesSum'45'NoMuNu_38 (coe v0) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.parseType-NoMuNu
d_parseType'45'NoMuNu_120 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
d_parseType'45'NoMuNu_120 v0 v1 v2 ~v3
  = du_parseType'45'NoMuNu_120 v0 v1 v2
du_parseType'45'NoMuNu_120 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
du_parseType'45'NoMuNu_120 v0 v1 v2
  = coe
      d_ParsesType'45'NoMuNu_66 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Grammar.ParserBridge.du_sound'45'type_842
         (coe v0))
-- Once.Grammar.ParserInvariant.parseTypeAtom-NoMuNu
d_parseTypeAtom'45'NoMuNu_132 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
d_parseTypeAtom'45'NoMuNu_132 v0 v1 v2 ~v3
  = du_parseTypeAtom'45'NoMuNu_132 v0 v1 v2
du_parseTypeAtom'45'NoMuNu_132 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoMuNu_512
du_parseTypeAtom'45'NoMuNu_132 v0 v1 v2
  = coe
      d_ParsesAtom'45'NoMuNu_12 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Grammar.ParserBridge.du_sound'45'atom_864
         (coe v0))
