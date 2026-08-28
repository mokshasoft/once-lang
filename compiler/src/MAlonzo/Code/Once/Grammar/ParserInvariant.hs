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

-- Once.Grammar.ParserInvariant.ParsesAtom-NoNu
d_ParsesAtom'45'NoNu_12 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
d_ParsesAtom'45'NoNu_12 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'unit_122
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'unit_872
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'void_126
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'void_874
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'int_130
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'int_876
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'float_134
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'float_878
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'buffer_138
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'buffer_882
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'string_142
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'str_880
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'eff_154 v5 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'eff_908
                           (d_ParsesAtom'45'NoNu_12 (coe v12) (coe v13) (coe v5) (coe v9))
                           (d_ParsesAtom'45'NoNu_12 (coe v5) (coe v15) (coe v2) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'io_162 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'eff_908
                           (coe MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'unit_872)
                           (d_ParsesAtom'45'NoNu_12 (coe v9) (coe v12) (coe v2) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_172 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    d_ParsesType'45'NoNu_66 (coe v11) (coe v1)
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'mu_180 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'mu_912
                    (coe du_ParsesFunctorSum'45'NoNuF_100 (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesProd-NoNu
d_ParsesProd'45'NoNu_20 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProd_98 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
d_ParsesProd'45'NoNu_20 v0 ~v1 ~v2 v3
  = du_ParsesProd'45'NoNu_20 v0 v3
du_ParsesProd'45'NoNu_20 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProd_98 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
du_ParsesProd'45'NoNu_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192 v3 v5 v7 v8
        -> coe
             du_ParsesProdTail'45'NoNu_30 (coe v3) (coe v8)
             (coe d_ParsesAtom'45'NoNu_12 (coe v0) (coe v5) (coe v3) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesProdTail-NoNu
d_ParsesProdTail'45'NoNu_30 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProdTail_100 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
d_ParsesProdTail'45'NoNu_30 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ParsesProdTail'45'NoNu_30 v1 v4 v5
du_ParsesProdTail'45'NoNu_30 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProdTail_100 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
du_ParsesProdTail'45'NoNu_30 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198 v5
        -> coe v2
      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'star_212 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    du_ParsesProdTail'45'NoNu_30 (coe v5) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'prod_888 v2
                       (d_ParsesAtom'45'NoNu_12 (coe v12) (coe v7) (coe v5) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesSum-NoNu
d_ParsesSum'45'NoNu_38 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSum_102 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
d_ParsesSum'45'NoNu_38 v0 ~v1 ~v2 v3
  = du_ParsesSum'45'NoNu_38 v0 v3
du_ParsesSum'45'NoNu_38 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSum_102 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
du_ParsesSum'45'NoNu_38 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224 v3 v5 v7 v8
        -> coe
             du_ParsesSumTail'45'NoNu_48 (coe v3) (coe v8)
             (coe du_ParsesProd'45'NoNu_20 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesSumTail-NoNu
d_ParsesSumTail'45'NoNu_48 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSumTail_104 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
d_ParsesSumTail'45'NoNu_48 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ParsesSumTail'45'NoNu_48 v1 v4 v5
du_ParsesSumTail'45'NoNu_48 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSumTail_104 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
du_ParsesSumTail'45'NoNu_48 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230 v5
        -> coe v2
      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'plus_244 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    du_ParsesSumTail'45'NoNu_48 (coe v5) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'sum_894 v2
                       (coe du_ParsesProd'45'NoNu_20 (coe v12) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesArrowTail-NoNu
d_ParsesArrowTail'45'NoNu_58 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesArrowTail_108 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
d_ParsesArrowTail'45'NoNu_58 ~v0 v1 v2 v3 v4 v5
  = du_ParsesArrowTail'45'NoNu_58 v1 v2 v3 v4 v5
du_ParsesArrowTail'45'NoNu_58 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesArrowTail_108 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
du_ParsesArrowTail'45'NoNu_58 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262 v7
        -> coe v4
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_274 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v12 of
                    (:) v13 v14
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'fun_902 v4
                                  (d_ParsesType'45'NoNu_66 (coe v14) (coe v17) (coe v2) (coe v10))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow_284 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_nnu'45'fun_902 v4
                           (d_ParsesType'45'NoNu_66 (coe v11) (coe v14) (coe v2) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesType-NoNu
d_ParsesType'45'NoNu_66 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
d_ParsesType'45'NoNu_66 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256 v5 v7 v9 v10
        -> coe
             du_ParsesArrowTail'45'NoNu_58 (coe v5) (coe v1) (coe v2) (coe v10)
             (coe du_ParsesSum'45'NoNu_38 (coe v0) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesFunctorAtom-NoNuF
d_ParsesFunctorAtom'45'NoNuF_74 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorAtom_110 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870
d_ParsesFunctorAtom'45'NoNuF_74 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'id_288
        -> coe MAlonzo.Code.Once.Grammar.Convert.C_nnuf'45'id_918
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'k_296 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_110 v10
                      -> coe
                           MAlonzo.Code.Once.Grammar.Convert.C_nnuf'45'k_916
                           (d_ParsesAtom'45'NoNu_12 (coe v9) (coe v10) (coe v2) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'paren_306 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> coe du_ParsesFunctorSum'45'NoNuF_100 (coe v11) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesFunctorProd-NoNuF
d_ParsesFunctorProd'45'NoNuF_82 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProd_112 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870
d_ParsesFunctorProd'45'NoNuF_82 v0 ~v1 ~v2 v3
  = du_ParsesFunctorProd'45'NoNuF_82 v0 v3
du_ParsesFunctorProd'45'NoNuF_82 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProd_112 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870
du_ParsesFunctorProd'45'NoNuF_82 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfp'45'mk_318 v3 v5 v7 v8
        -> coe
             du_ParsesFunctorProdTail'45'NoNuF_92 (coe v3) (coe v8)
             (coe
                d_ParsesFunctorAtom'45'NoNuF_74 (coe v0) (coe v5) (coe v3)
                (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesFunctorProdTail-NoNuF
d_ParsesFunctorProdTail'45'NoNuF_92 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProdTail_114 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870
d_ParsesFunctorProdTail'45'NoNuF_92 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ParsesFunctorProdTail'45'NoNuF_92 v1 v4 v5
du_ParsesFunctorProdTail'45'NoNuF_92 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProdTail_114 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870
du_ParsesFunctorProdTail'45'NoNuF_92 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324 v5
        -> coe v2
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'star_338 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    du_ParsesFunctorProdTail'45'NoNuF_92 (coe v5) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Grammar.Convert.C_nnuf'45'prod_930 v2
                       (d_ParsesFunctorAtom'45'NoNuF_74
                          (coe v12) (coe v7) (coe v5) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesFunctorSum-NoNuF
d_ParsesFunctorSum'45'NoNuF_100 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSum_116 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870
d_ParsesFunctorSum'45'NoNuF_100 v0 ~v1 ~v2 v3
  = du_ParsesFunctorSum'45'NoNuF_100 v0 v3
du_ParsesFunctorSum'45'NoNuF_100 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSum_116 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870
du_ParsesFunctorSum'45'NoNuF_100 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfs'45'mk_350 v3 v5 v7 v8
        -> coe
             du_ParsesFunctorSumTail'45'NoNuF_110 (coe v3) (coe v8)
             (coe du_ParsesFunctorProd'45'NoNuF_82 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.ParsesFunctorSumTail-NoNuF
d_ParsesFunctorSumTail'45'NoNuF_110 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSumTail_118 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870
d_ParsesFunctorSumTail'45'NoNuF_110 ~v0 v1 ~v2 ~v3 v4 v5
  = du_ParsesFunctorSumTail'45'NoNuF_110 v1 v4 v5
du_ParsesFunctorSumTail'45'NoNuF_110 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSumTail_118 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNuF_870
du_ParsesFunctorSumTail'45'NoNuF_110 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356 v5
        -> coe v2
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'plus_370 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    du_ParsesFunctorSumTail'45'NoNuF_110 (coe v5) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Grammar.Convert.C_nnuf'45'sum_924 v2
                       (coe du_ParsesFunctorProd'45'NoNuF_82 (coe v12) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserInvariant.parseType-NoNu
d_parseType'45'NoNu_194 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
d_parseType'45'NoNu_194 v0 v1 v2 ~v3
  = du_parseType'45'NoNu_194 v0 v1 v2
du_parseType'45'NoNu_194 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
du_parseType'45'NoNu_194 v0 v1 v2
  = coe
      d_ParsesType'45'NoNu_66 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Grammar.ParserBridge.du_sound'45'type_1162
         (coe v0))
-- Once.Grammar.ParserInvariant.parseTypeAtom-NoNu
d_parseTypeAtom'45'NoNu_206 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
d_parseTypeAtom'45'NoNu_206 v0 v1 v2 ~v3
  = du_parseTypeAtom'45'NoNu_206 v0 v1 v2
du_parseTypeAtom'45'NoNu_206 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Grammar.Convert.T_NoNu_868
du_parseTypeAtom'45'NoNu_206 v0 v1 v2
  = coe
      d_ParsesAtom'45'NoNu_12 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Grammar.ParserBridge.du_sound'45'atom_1184
         (coe v0))
