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
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Grammar.ParserInvariant.ParsesAtom-Expressible
d_ParsesAtom'45'Expressible_12 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
d_ParsesAtom'45'Expressible_12 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'unit_122
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_ex'45'unit_1102
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'void_126
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_ex'45'void_1104
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'int_130
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_ex'45'int_1106
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'float_134
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_ex'45'float_1108
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'eff_146 v5 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_ex'45'eff_1134
                           (d_ParsesAtom'45'Expressible_12
                              (coe v12) (coe v13) (coe v5) (coe v9))
                           (d_ParsesAtom'45'Expressible_12
                              (coe v5) (coe v15) (coe v2) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'act_158 v5 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_ex'45'act_1148
                           (d_ParsesAtom'45'Expressible_12
                              (coe v12) (coe v13) (coe v5) (coe v9))
                           (d_ParsesAtom'45'Expressible_12
                              (coe v5) (coe v15) (coe v2) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_168 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    d_ParsesType'45'Expressible_66 (coe v11) (coe v1)
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'mu_176 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Once.Grammar.Convert.C_ex'45'mu_1138
                    (coe du_ParsesFunctorSum'45'ExpressibleF_100 (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'nu_184 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Once.Grammar.Convert.C_ex'45'nu_1142
                    (coe du_ParsesFunctorSum'45'ExpressibleF_100 (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'nu'45'act_192 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v9 of
                    (:) v10 v11
                      -> case coe v11 of
                           (:) v12 v13
                             -> coe
                                  MAlonzo.Code.Once.Grammar.Convert.C_ex'45'nu'45'act_1152
                                  (coe du_ParsesFunctorSum'45'ExpressibleF_100 (coe v13) (coe v7))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesProd-Expressible
d_ParsesProd'45'Expressible_20 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProd_98 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
d_ParsesProd'45'Expressible_20 v0 ~v1 ~v2 v3
  = du_ParsesProd'45'Expressible_20 v0 v3
du_ParsesProd'45'Expressible_20 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProd_98 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
du_ParsesProd'45'Expressible_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_204 v3 v5 v7 v8
        -> coe
             du_ParsesProdTail'45'Expressible_30 (coe v3) (coe v8)
             (coe
                d_ParsesAtom'45'Expressible_12 (coe v0) (coe v5) (coe v3) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesProdTail-Expressible
d_ParsesProdTail'45'Expressible_30 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProdTail_100 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
d_ParsesProdTail'45'Expressible_30 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ParsesProdTail'45'Expressible_30 v1 v4 v5
du_ParsesProdTail'45'Expressible_30 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProdTail_100 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
du_ParsesProdTail'45'Expressible_30 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_210 v5
        -> coe v2
      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'star_224 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    du_ParsesProdTail'45'Expressible_30 (coe v5) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Grammar.Convert.C_ex'45'prod_1114 v2
                       (d_ParsesAtom'45'Expressible_12
                          (coe v12) (coe v7) (coe v5) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesSum-Expressible
d_ParsesSum'45'Expressible_38 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSum_102 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
d_ParsesSum'45'Expressible_38 v0 ~v1 ~v2 v3
  = du_ParsesSum'45'Expressible_38 v0 v3
du_ParsesSum'45'Expressible_38 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSum_102 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
du_ParsesSum'45'Expressible_38 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_236 v3 v5 v7 v8
        -> coe
             du_ParsesSumTail'45'Expressible_48 (coe v3) (coe v8)
             (coe du_ParsesProd'45'Expressible_20 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesSumTail-Expressible
d_ParsesSumTail'45'Expressible_48 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSumTail_104 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
d_ParsesSumTail'45'Expressible_48 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ParsesSumTail'45'Expressible_48 v1 v4 v5
du_ParsesSumTail'45'Expressible_48 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSumTail_104 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
du_ParsesSumTail'45'Expressible_48 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_242 v5
        -> coe v2
      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'plus_256 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    du_ParsesSumTail'45'Expressible_48 (coe v5) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Grammar.Convert.C_ex'45'sum_1120 v2
                       (coe du_ParsesProd'45'Expressible_20 (coe v12) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesArrowTail-Expressible
d_ParsesArrowTail'45'Expressible_58 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesArrowTail_108 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
d_ParsesArrowTail'45'Expressible_58 ~v0 v1 v2 v3 v4 v5
  = du_ParsesArrowTail'45'Expressible_58 v1 v2 v3 v4 v5
du_ParsesArrowTail'45'Expressible_58 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesArrowTail_108 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
du_ParsesArrowTail'45'Expressible_58 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_274 v7
        -> coe v4
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_286 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v12 of
                    (:) v13 v14
                      -> case coe v1 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.Grammar.Convert.C_ex'45'fun_1128 v4
                                  (d_ParsesType'45'Expressible_66
                                     (coe v14) (coe v17) (coe v2) (coe v10))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow_296 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_ex'45'fun_1128 v4
                           (d_ParsesType'45'Expressible_66
                              (coe v11) (coe v14) (coe v2) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesType-Expressible
d_ParsesType'45'Expressible_66 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
d_ParsesType'45'Expressible_66 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_268 v5 v7 v9 v10
        -> coe
             du_ParsesArrowTail'45'Expressible_58 (coe v5) (coe v1) (coe v2)
             (coe v10) (coe du_ParsesSum'45'Expressible_38 (coe v0) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesFunctorAtom-ExpressibleF
d_ParsesFunctorAtom'45'ExpressibleF_74 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorAtom_110 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100
d_ParsesFunctorAtom'45'ExpressibleF_74 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'id_300
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_exf'45'id_1158
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'k_308 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C_K_38 v10
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_exf'45'k_1156
                           (d_ParsesAtom'45'Expressible_12
                              (coe v9) (coe v10) (coe v2) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'paren_318 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> coe du_ParsesFunctorSum'45'ExpressibleF_100 (coe v11) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesFunctorProd-ExpressibleF
d_ParsesFunctorProd'45'ExpressibleF_82 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProd_112 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100
d_ParsesFunctorProd'45'ExpressibleF_82 v0 ~v1 ~v2 v3
  = du_ParsesFunctorProd'45'ExpressibleF_82 v0 v3
du_ParsesFunctorProd'45'ExpressibleF_82 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProd_112 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100
du_ParsesFunctorProd'45'ExpressibleF_82 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfp'45'mk_330 v3 v5 v7 v8
        -> coe
             du_ParsesFunctorProdTail'45'ExpressibleF_92 (coe v3) (coe v8)
             (coe
                d_ParsesFunctorAtom'45'ExpressibleF_74 (coe v0) (coe v5) (coe v3)
                (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesFunctorProdTail-ExpressibleF
d_ParsesFunctorProdTail'45'ExpressibleF_92 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProdTail_114 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100
d_ParsesFunctorProdTail'45'ExpressibleF_92 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ParsesFunctorProdTail'45'ExpressibleF_92 v1 v4 v5
du_ParsesFunctorProdTail'45'ExpressibleF_92 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProdTail_114 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100
du_ParsesFunctorProdTail'45'ExpressibleF_92 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_336 v5
        -> coe v2
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'star_350 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    du_ParsesFunctorProdTail'45'ExpressibleF_92 (coe v5) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Grammar.Convert.C_exf'45'prod_1170 v2
                       (d_ParsesFunctorAtom'45'ExpressibleF_74
                          (coe v12) (coe v7) (coe v5) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesFunctorSum-ExpressibleF
d_ParsesFunctorSum'45'ExpressibleF_100 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSum_116 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100
d_ParsesFunctorSum'45'ExpressibleF_100 v0 ~v1 ~v2 v3
  = du_ParsesFunctorSum'45'ExpressibleF_100 v0 v3
du_ParsesFunctorSum'45'ExpressibleF_100 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSum_116 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100
du_ParsesFunctorSum'45'ExpressibleF_100 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfs'45'mk_362 v3 v5 v7 v8
        -> coe
             du_ParsesFunctorSumTail'45'ExpressibleF_110 (coe v3) (coe v8)
             (coe du_ParsesFunctorProd'45'ExpressibleF_82 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesFunctorSumTail-ExpressibleF
d_ParsesFunctorSumTail'45'ExpressibleF_110 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSumTail_118 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100
d_ParsesFunctorSumTail'45'ExpressibleF_110 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ParsesFunctorSumTail'45'ExpressibleF_110 v1 v4 v5
du_ParsesFunctorSumTail'45'ExpressibleF_110 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSumTail_118 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100 ->
  MAlonzo.Code.Once.Grammar.Convert.T_ExpressibleF_1100
du_ParsesFunctorSumTail'45'ExpressibleF_110 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_368 v5
        -> coe v2
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'plus_382 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    du_ParsesFunctorSumTail'45'ExpressibleF_110 (coe v5) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Grammar.Convert.C_exf'45'sum_1164 v2
                       (coe du_ParsesFunctorProd'45'ExpressibleF_82 (coe v12) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.parseType-Expressible
d_parseType'45'Expressible_200 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
d_parseType'45'Expressible_200 v0 v1 v2 ~v3
  = du_parseType'45'Expressible_200 v0 v1 v2
du_parseType'45'Expressible_200 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
du_parseType'45'Expressible_200 v0 v1 v2
  = coe
      d_ParsesType'45'Expressible_66 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Grammar.ParserBridge.du_sound'45'type_1322
         (coe v0))
-- Once.Grammar.ParserInvariant.parseTypeAtom-Expressible
d_parseTypeAtom'45'Expressible_212 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
d_parseTypeAtom'45'Expressible_212 v0 v1 v2 ~v3
  = du_parseTypeAtom'45'Expressible_212 v0 v1 v2
du_parseTypeAtom'45'Expressible_212 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Grammar.Convert.T_Expressible_1098
du_parseTypeAtom'45'Expressible_212 v0 v1 v2
  = coe
      d_ParsesAtom'45'Expressible_12 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Grammar.ParserBridge.du_sound'45'atom_1344
         (coe v0))
