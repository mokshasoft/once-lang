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

module MAlonzo.Code.Once.Grammar.RelRoundtrip where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ParserRelation
import qualified MAlonzo.Code.Once.Grammar.Printer
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Type

-- Once.Grammar.RelRoundtrip.quantityToken≡quantityTokenOf
d_quantityToken'8801'quantityTokenOf_8 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_quantityToken'8801'quantityTokenOf_8 = erased
-- Once.Grammar.RelRoundtrip.NotCont→NotStar
d_NotCont'8594'NotStar_12 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> AgdaAny -> AgdaAny
d_NotCont'8594'NotStar_12 v0 ~v1 = du_NotCont'8594'NotStar_12 v0
du_NotCont'8594'NotStar_12 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> AgdaAny
du_NotCont'8594'NotStar_12 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v1 v2
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.RelRoundtrip.NotCont→NotStarPlus
d_NotCont'8594'NotStarPlus_16 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> AgdaAny -> AgdaAny
d_NotCont'8594'NotStarPlus_16 v0 ~v1
  = du_NotCont'8594'NotStarPlus_16 v0
du_NotCont'8594'NotStarPlus_16 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> AgdaAny
du_NotCont'8594'NotStarPlus_16 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v1 v2
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.RelRoundtrip.NotCont→NotStar-quantity
d_NotCont'8594'NotStar'45'quantity_22 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> AgdaAny
d_NotCont'8594'NotStar'45'quantity_22 v0 ~v1
  = du_NotCont'8594'NotStar'45'quantity_22 v0
du_NotCont'8594'NotStar'45'quantity_22 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 -> AgdaAny
du_NotCont'8594'NotStar'45'quantity_22 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Grammar.RelRoundtrip.NotCont→NotStarPlus-quantity
d_NotCont'8594'NotStarPlus'45'quantity_28 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> AgdaAny
d_NotCont'8594'NotStarPlus'45'quantity_28 v0 ~v1
  = du_NotCont'8594'NotStarPlus'45'quantity_28 v0
du_NotCont'8594'NotStarPlus'45'quantity_28 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 -> AgdaAny
du_NotCont'8594'NotStarPlus'45'quantity_28 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Grammar.RelRoundtrip.NotCont→NotArrowOrGrade
d_NotCont'8594'NotArrowOrGrade_32 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> AgdaAny -> AgdaAny
d_NotCont'8594'NotArrowOrGrade_32 v0 ~v1
  = du_NotCont'8594'NotArrowOrGrade_32 v0
du_NotCont'8594'NotArrowOrGrade_32 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> AgdaAny
du_NotCont'8594'NotArrowOrGrade_32 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v1 v2
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.RelRoundtrip.rt-atom
d_rt'45'atom_40 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96
d_rt'45'atom_40 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'unit_76
        -> coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'unit_122
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'void_78
        -> coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'void_126
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'int_80
        -> coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'int_130
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'float_82
        -> coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'float_134
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'buffer_84
        -> coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'buffer_138
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'string_86
        -> coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'string_142
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'prod_92 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C__'8855'__26 v7 v8
               -> coe
                    MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_172
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       du_rt'45'type'45'of'45'prod_52 (coe v7) (coe v8) (coe v5) (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'sum_98 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C__'8853'__28 v7 v8
               -> coe
                    MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_172
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       du_rt'45'type'45'of'45'sum_64 (coe v7) (coe v8) (coe v5) (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'fun_106 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__24 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_172
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       du_rt'45'type'45'of'45'fun_78 (coe v8) (coe v10) (coe v6) (coe v7)
                       (coe v9)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'eff_112 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_TEff_30 v7 v8
               -> coe
                    MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_172
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                          (coe
                             MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v7)
                             (coe v5))
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                          (coe
                             MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v8)
                             (coe v6)))
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                             (coe
                                MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v7)
                                (coe v5))
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_eff_36))
                             (coe
                                MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v8)
                                (coe v6)))
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                (coe
                                   MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v7)
                                   (coe v5))
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                                   (coe MAlonzo.Code.Once.Type.C_eff_36))
                                (coe
                                   MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v8)
                                   (coe v6)))
                             (coe
                                MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'eff_154
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v8))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2)))
                                (d_rt'45'atom_40
                                   (coe v7) (coe v5)
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v8))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                         (coe v2))))
                                (d_rt'45'atom_40
                                   (coe v8) (coe v6)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))))
                             (coe
                                MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.RelRoundtrip.rt-type-of-prod
d_rt'45'type'45'of'45'prod_52 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
d_rt'45'type'45'of'45'prod_52 v0 v1 v2 v3 v4 ~v5
  = du_rt'45'type'45'of'45'prod_52 v0 v1 v2 v3 v4
du_rt'45'type'45'of'45'prod_52 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
du_rt'45'type'45'of'45'prod_52 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256 v4
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe
            MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v0)
            (coe v2))
         (coe
            MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v1)
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224 v4
         (coe
            MAlonzo.Code.Once.Type.C__'42'__122
            (coe
               MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v0)
               (coe v2))
            (coe
               MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v1)
               (coe v3)))
         (coe
            MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Once.Parser.Token.C_TStar_52)
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v1))
                  (coe v4)))
            (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
               (coe v0) (coe v2))
            (d_rt'45'atom_40
               (coe v0) (coe v2)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.Parser.Token.C_TStar_52)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v1))
                     (coe v4))))
            (coe
               MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'star_212 v4
               (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
                  (coe v1) (coe v3))
               (d_rt'45'atom_40 (coe v1) (coe v3) (coe v4))
               (coe
                  MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                  (coe du_NotCont'8594'NotStar_12 (coe v4)))))
         (coe
            MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
            (coe du_NotCont'8594'NotStarPlus_16 (coe v4))))
      (coe
         MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
         (coe du_NotCont'8594'NotArrowOrGrade_32 (coe v4)))
-- Once.Grammar.RelRoundtrip.rt-type-of-sum
d_rt'45'type'45'of'45'sum_64 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
d_rt'45'type'45'of'45'sum_64 v0 v1 v2 v3 v4 ~v5
  = du_rt'45'type'45'of'45'sum_64 v0 v1 v2 v3 v4
du_rt'45'type'45'of'45'sum_64 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
du_rt'45'type'45'of'45'sum_64 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256 v4
      (coe
         MAlonzo.Code.Once.Type.C__'43'__124
         (coe
            MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v0)
            (coe v2))
         (coe
            MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v1)
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48)
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v1))
               (coe v4)))
         (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
            (coe v0) (coe v2))
         (coe
            MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48)
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v1))
                  (coe v4)))
            (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
               (coe v0) (coe v2))
            (d_rt'45'atom_40
               (coe v0) (coe v2)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v1))
                     (coe v4))))
            (coe
               MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
         (coe
            MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'plus_244 v4
            (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
               (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192 v4
               (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
                  (coe v1) (coe v3))
               (d_rt'45'atom_40 (coe v1) (coe v3) (coe v4))
               (coe
                  MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                  (coe du_NotCont'8594'NotStar_12 (coe v4))))
            (coe
               MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
               (coe du_NotCont'8594'NotStarPlus_16 (coe v4)))))
      (coe
         MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
         (coe du_NotCont'8594'NotArrowOrGrade_32 (coe v4)))
-- Once.Grammar.RelRoundtrip.rt-type-of-fun
d_rt'45'type'45'of'45'fun_78 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
d_rt'45'type'45'of'45'fun_78 v0 v1 v2 v3 v4 v5 ~v6
  = du_rt'45'type'45'of'45'fun_78 v0 v1 v2 v3 v4 v5
du_rt'45'type'45'of'45'fun_78 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
du_rt'45'type'45'of'45'fun_78 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Parser.TypeRelation.d_quantityTokenOf_94
            (coe v4))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v1))
               (coe v5))))
      (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
         (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Parser.TypeRelation.d_quantityTokenOf_94
               (coe v4))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v1))
                  (coe v5))))
         (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
            (coe v0) (coe v2))
         (coe
            MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Parser.TypeRelation.d_quantityTokenOf_94
                  (coe v4))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v1))
                     (coe v5))))
            (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
               (coe v0) (coe v2))
            (d_rt'45'atom_40
               (coe v0) (coe v2)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Parser.TypeRelation.d_quantityTokenOf_94
                     (coe v4))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v1))
                        (coe v5)))))
            (coe
               MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
               (coe du_NotCont'8594'NotStar'45'quantity_22 (coe v4))))
         (coe
            MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
            (coe du_NotCont'8594'NotStarPlus'45'quantity_28 (coe v4))))
      (coe
         MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_274
         (coe du_rt'45'type_86 (coe v1) (coe v3) (coe v5)))
-- Once.Grammar.RelRoundtrip.rt-type
d_rt'45'type_86 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
d_rt'45'type_86 v0 v1 v2 ~v3 = du_rt'45'type_86 v0 v1 v2
du_rt'45'type_86 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
du_rt'45'type_86 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256 v2
      (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224 v2
         (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192 v2
            (MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8
               (coe v0) (coe v1))
            (d_rt'45'atom_40 (coe v0) (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
               (coe du_NotCont'8594'NotStar_12 (coe v2))))
         (coe
            MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
            (coe du_NotCont'8594'NotStarPlus_16 (coe v2))))
      (coe
         MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
         (coe du_NotCont'8594'NotArrowOrGrade_32 (coe v2)))
-- Once.Grammar.RelRoundtrip.round-trip-rel
d_round'45'trip'45'rel_226 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_74 ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
d_round'45'trip'45'rel_226 v0 v1
  = coe
      du_rt'45'type_86 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
