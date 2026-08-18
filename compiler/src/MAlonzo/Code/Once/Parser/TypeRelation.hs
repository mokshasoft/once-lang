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

module MAlonzo.Code.Once.Parser.TypeRelation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type

-- Once.Parser.TypeRelation.NotStar
d_NotStar_6 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotStar_6 = erased
-- Once.Parser.TypeRelation.NotStarPlus
d_NotStarPlus_20 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotStarPlus_20 = erased
-- Once.Parser.TypeRelation.NotArrowOrGrade
d_NotArrowOrGrade_34 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotArrowOrGrade_34 = erased
-- Once.Parser.TypeRelation.NotCont
d_NotCont_60 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotCont_60 = erased
-- Once.Parser.TypeRelation.quantityTokenOf
d_quantityTokenOf_94 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6
d_quantityTokenOf_94 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Zero_6
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
      MAlonzo.Code.Once.Type.C_One_8
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
      MAlonzo.Code.Once.Type.C_Many_10
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesAtom
d_ParsesAtom_96 a0 a1 a2 = ()
data T_ParsesAtom_96
  = C_pa'45'unit_122 | C_pa'45'void_126 | C_pa'45'int_130 |
    C_pa'45'float_134 | C_pa'45'buffer_138 | C_pa'45'string_142 |
    C_pa'45'eff_154 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAtom_96 T_ParsesAtom_96 |
    C_pa'45'io_162 T_ParsesAtom_96 |
    C_pa'45'paren_172 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      T_ParsesType_106 |
    C_pa'45'mu_180 T_ParsesFunctorSum_116
-- Once.Parser.TypeRelation.ParsesProd
d_ParsesProd_98 a0 a1 a2 = ()
data T_ParsesProd_98
  = C_pp'45'mk_192 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Type.T_Type_112 T_ParsesAtom_96
                   T_ParsesProdTail_100
-- Once.Parser.TypeRelation.ParsesProdTail
d_ParsesProdTail_100 a0 a1 a2 a3 = ()
data T_ParsesProdTail_100
  = C_ppt'45'done_198 AgdaAny |
    C_ppt'45'star_212 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Type.T_Type_112 T_ParsesAtom_96
                      T_ParsesProdTail_100
-- Once.Parser.TypeRelation.ParsesSum
d_ParsesSum_102 a0 a1 a2 = ()
data T_ParsesSum_102
  = C_ps'45'mk_224 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Type.T_Type_112 T_ParsesProd_98
                   T_ParsesSumTail_104
-- Once.Parser.TypeRelation.ParsesSumTail
d_ParsesSumTail_104 a0 a1 a2 a3 = ()
data T_ParsesSumTail_104
  = C_pst'45'done_230 AgdaAny |
    C_pst'45'plus_244 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Type.T_Type_112 T_ParsesProd_98
                      T_ParsesSumTail_104
-- Once.Parser.TypeRelation.ParsesType
d_ParsesType_106 a0 a1 a2 = ()
data T_ParsesType_106
  = C_pt'45'mk_256 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Type.T_Type_112 T_ParsesSum_102
                   T_ParsesArrowTail_108
-- Once.Parser.TypeRelation.ParsesArrowTail
d_ParsesArrowTail_108 a0 a1 a2 a3 = ()
data T_ParsesArrowTail_108
  = C_pat'45'done_262 AgdaAny |
    C_pat'45'arrow'45'g_274 T_ParsesType_106 |
    C_pat'45'arrow_284 T_ParsesType_106
-- Once.Parser.TypeRelation.ParsesFunctorAtom
d_ParsesFunctorAtom_110 a0 a1 a2 = ()
data T_ParsesFunctorAtom_110
  = C_pfa'45'id_288 | C_pfa'45'k_296 T_ParsesAtom_96 |
    C_pfa'45'paren_306 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       T_ParsesFunctorSum_116
-- Once.Parser.TypeRelation.ParsesFunctorProd
d_ParsesFunctorProd_112 a0 a1 a2 = ()
data T_ParsesFunctorProd_112
  = C_pfp'45'mk_318 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    MAlonzo.Code.Once.Type.T_Functor_110 T_ParsesFunctorAtom_110
                    T_ParsesFunctorProdTail_114
-- Once.Parser.TypeRelation.ParsesFunctorProdTail
d_ParsesFunctorProdTail_114 a0 a1 a2 a3 = ()
data T_ParsesFunctorProdTail_114
  = C_pfpt'45'done_324 AgdaAny |
    C_pfpt'45'star_338 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Type.T_Functor_110 T_ParsesFunctorAtom_110
                       T_ParsesFunctorProdTail_114
-- Once.Parser.TypeRelation.ParsesFunctorSum
d_ParsesFunctorSum_116 a0 a1 a2 = ()
data T_ParsesFunctorSum_116
  = C_pfs'45'mk_350 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    MAlonzo.Code.Once.Type.T_Functor_110 T_ParsesFunctorProd_112
                    T_ParsesFunctorSumTail_118
-- Once.Parser.TypeRelation.ParsesFunctorSumTail
d_ParsesFunctorSumTail_118 a0 a1 a2 a3 = ()
data T_ParsesFunctorSumTail_118
  = C_pfst'45'done_356 AgdaAny |
    C_pfst'45'plus_370 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Type.T_Functor_110 T_ParsesFunctorProd_112
                       T_ParsesFunctorSumTail_118
-- Once.Parser.TypeRelation.ParsesAtom-shrinks
d_ParsesAtom'45'shrinks_378 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAtom_96 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAtom'45'shrinks_378 v0 v1 v2 v3
  = case coe v3 of
      C_pa'45'unit_122
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'void_126
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'int_130
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'float_134
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'buffer_138
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'string_142
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'eff_154 v5 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
                           (coe
                              d_ParsesAtom'45'shrinks_378 (coe v5) (coe v15) (coe v2) (coe v10))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                              (coe
                                 d_ParsesAtom'45'shrinks_378 (coe v12) (coe v13) (coe v5) (coe v9))
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                 (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                       (let v16 = \ v16 -> addInt (coe (1 :: Integer)) (coe v16) in
                                        coe (coe (\ v17 -> v16)))
                                       (coe (0 :: Integer)) (coe v12)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'io_162 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                           (coe
                              d_ParsesAtom'45'shrinks_378 (coe v9) (coe v12) (coe v2) (coe v7))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                     coe (coe (\ v14 -> v13)))
                                    (coe (0 :: Integer)) (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'paren_172 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_foldr_216
                          (coe (\ v12 v13 -> addInt (coe (1 :: Integer)) (coe v13)))
                          (coe (0 :: Integer)) (coe v2)))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (coe (\ v12 v13 -> addInt (coe (1 :: Integer)) (coe v13)))
                             (coe (0 :: Integer)) (coe v2))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                       (coe
                          d_ParsesType'45'shrinks_432 (coe v11) (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                          (coe v8))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                 coe (coe (\ v13 -> v12)))
                                (coe (0 :: Integer)) (coe v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'mu_180 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesFunctorSum'45'shrinks_466 (coe v9) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesProd-shrinks
d_ParsesProd'45'shrinks_386 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProd_98 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesProd'45'shrinks_386 v0 ~v1 ~v2 v3
  = du_ParsesProd'45'shrinks_386 v0 v3
du_ParsesProd'45'shrinks_386 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProd_98 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesProd'45'shrinks_386 v0 v1
  = case coe v1 of
      C_pp'45'mk_192 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesProdTail'45'shrinks_396 (coe v3) (coe v8))
             (coe
                d_ParsesAtom'45'shrinks_378 (coe v0) (coe v5) (coe v3) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesProdTail-shrinks
d_ParsesProdTail'45'shrinks_396 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdTail_100 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesProdTail'45'shrinks_396 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesProdTail'45'shrinks_396 v1 v4
du_ParsesProdTail'45'shrinks_396 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdTail_100 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesProdTail'45'shrinks_396 v0 v1
  = case coe v1 of
      C_ppt'45'done_198 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_ppt'45'star_212 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesProdTail'45'shrinks_396 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe
                             d_ParsesAtom'45'shrinks_378 (coe v11) (coe v6) (coe v4) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesSum-shrinks
d_ParsesSum'45'shrinks_404 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSum_102 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesSum'45'shrinks_404 v0 ~v1 ~v2 v3
  = du_ParsesSum'45'shrinks_404 v0 v3
du_ParsesSum'45'shrinks_404 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSum_102 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesSum'45'shrinks_404 v0 v1
  = case coe v1 of
      C_ps'45'mk_224 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesSumTail'45'shrinks_414 (coe v3) (coe v8))
             (coe du_ParsesProd'45'shrinks_386 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesSumTail-shrinks
d_ParsesSumTail'45'shrinks_414 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumTail_104 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesSumTail'45'shrinks_414 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesSumTail'45'shrinks_414 v1 v4
du_ParsesSumTail'45'shrinks_414 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumTail_104 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesSumTail'45'shrinks_414 v0 v1
  = case coe v1 of
      C_pst'45'done_230 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pst'45'plus_244 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesSumTail'45'shrinks_414 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesProd'45'shrinks_386 (coe v11) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesArrowTail-shrinks
d_ParsesArrowTail'45'shrinks_424 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesArrowTail_108 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesArrowTail'45'shrinks_424 ~v0 v1 v2 v3 v4
  = du_ParsesArrowTail'45'shrinks_424 v1 v2 v3 v4
du_ParsesArrowTail'45'shrinks_424 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesArrowTail_108 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesArrowTail'45'shrinks_424 v0 v1 v2 v3
  = case coe v3 of
      C_pat'45'done_262 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pat'45'arrow'45'g_274 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v11 of
                    (:) v12 v13
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                    -> coe
                                         seq (coe v17)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                            (coe
                                               MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                               (coe MAlonzo.Code.Data.List.Base.du_length_268 v13)
                                               (coe
                                                  d_ParsesType'45'shrinks_432 (coe v13) (coe v16)
                                                  (coe v2) (coe v9))
                                               (coe
                                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                  (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                        (let v19
                                                               = \ v19 ->
                                                                   addInt
                                                                     (coe (1 :: Integer))
                                                                     (coe v19) in
                                                         coe (coe (\ v20 -> v19)))
                                                        (coe (0 :: Integer)) (coe v13))))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pat'45'arrow_284 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                              (coe
                                 d_ParsesType'45'shrinks_432 (coe v10) (coe v13) (coe v2) (coe v8))
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                 (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                       (let v14 = \ v14 -> addInt (coe (1 :: Integer)) (coe v14) in
                                        coe (coe (\ v15 -> v14)))
                                       (coe (0 :: Integer)) (coe v10)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesType-shrinks
d_ParsesType'45'shrinks_432 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesType_106 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesType'45'shrinks_432 v0 v1 v2 v3
  = case coe v3 of
      C_pt'45'mk_256 v5 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe
                du_ParsesArrowTail'45'shrinks_424 (coe v5) (coe v1) (coe v2)
                (coe v10))
             (coe du_ParsesSum'45'shrinks_404 (coe v0) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesFunctorAtom-shrinks
d_ParsesFunctorAtom'45'shrinks_440 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFunctorAtom_110 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesFunctorAtom'45'shrinks_440 v0 v1 v2 v3
  = case coe v3 of
      C_pfa'45'id_288
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pfa'45'k_296 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v10
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                           (coe
                              d_ParsesAtom'45'shrinks_378 (coe v9) (coe v10) (coe v2) (coe v7))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (let v11 = \ v11 -> addInt (coe (1 :: Integer)) (coe v11) in
                                     coe (coe (\ v12 -> v11)))
                                    (coe (0 :: Integer)) (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pfa'45'paren_306 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_foldr_216
                          (coe (\ v12 v13 -> addInt (coe (1 :: Integer)) (coe v13)))
                          (coe (0 :: Integer)) (coe v2)))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (coe (\ v12 v13 -> addInt (coe (1 :: Integer)) (coe v13)))
                             (coe (0 :: Integer)) (coe v2))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                       (coe du_ParsesFunctorSum'45'shrinks_466 (coe v11) (coe v8))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                 coe (coe (\ v13 -> v12)))
                                (coe (0 :: Integer)) (coe v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesFunctorProd-shrinks
d_ParsesFunctorProd'45'shrinks_448 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFunctorProd_112 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesFunctorProd'45'shrinks_448 v0 ~v1 ~v2 v3
  = du_ParsesFunctorProd'45'shrinks_448 v0 v3
du_ParsesFunctorProd'45'shrinks_448 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFunctorProd_112 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesFunctorProd'45'shrinks_448 v0 v1
  = case coe v1 of
      C_pfp'45'mk_318 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesFunctorProdTail'45'shrinks_458 (coe v3) (coe v8))
             (coe
                d_ParsesFunctorAtom'45'shrinks_440 (coe v0) (coe v5) (coe v3)
                (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesFunctorProdTail-shrinks
d_ParsesFunctorProdTail'45'shrinks_458 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFunctorProdTail_114 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesFunctorProdTail'45'shrinks_458 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesFunctorProdTail'45'shrinks_458 v1 v4
du_ParsesFunctorProdTail'45'shrinks_458 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFunctorProdTail_114 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesFunctorProdTail'45'shrinks_458 v0 v1
  = case coe v1 of
      C_pfpt'45'done_324 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pfpt'45'star_338 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesFunctorProdTail'45'shrinks_458 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe
                             d_ParsesFunctorAtom'45'shrinks_440 (coe v11) (coe v6) (coe v4)
                             (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesFunctorSum-shrinks
d_ParsesFunctorSum'45'shrinks_466 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFunctorSum_116 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesFunctorSum'45'shrinks_466 v0 ~v1 ~v2 v3
  = du_ParsesFunctorSum'45'shrinks_466 v0 v3
du_ParsesFunctorSum'45'shrinks_466 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFunctorSum_116 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesFunctorSum'45'shrinks_466 v0 v1
  = case coe v1 of
      C_pfs'45'mk_350 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesFunctorSumTail'45'shrinks_476 (coe v3) (coe v8))
             (coe du_ParsesFunctorProd'45'shrinks_448 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesFunctorSumTail-shrinks
d_ParsesFunctorSumTail'45'shrinks_476 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFunctorSumTail_118 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesFunctorSumTail'45'shrinks_476 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesFunctorSumTail'45'shrinks_476 v1 v4
du_ParsesFunctorSumTail'45'shrinks_476 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFunctorSumTail_118 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesFunctorSumTail'45'shrinks_476 v0 v1
  = case coe v1 of
      C_pfst'45'done_356 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pfst'45'plus_370 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesFunctorSumTail'45'shrinks_476 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesFunctorProd'45'shrinks_448 (coe v11) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
