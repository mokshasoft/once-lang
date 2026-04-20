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
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaret0_30
      MAlonzo.Code.Once.Type.C_One_8
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaret1_28
      MAlonzo.Code.Once.Type.C_Many_10
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaretW_32
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesAtom
d_ParsesAtom_96 a0 a1 a2 = ()
data T_ParsesAtom_96
  = C_pa'45'unit_112 | C_pa'45'void_116 | C_pa'45'int_120 |
    C_pa'45'float_124 | C_pa'45'buffer_128 | C_pa'45'string_132 |
    C_pa'45'eff_144 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAtom_96 T_ParsesAtom_96 |
    C_pa'45'io_152 T_ParsesAtom_96 |
    C_pa'45'paren_162 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      T_ParsesType_106
-- Once.Parser.TypeRelation.ParsesProd
d_ParsesProd_98 a0 a1 a2 = ()
data T_ParsesProd_98
  = C_pp'45'mk_174 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Type.T_Type_38 T_ParsesAtom_96
                   T_ParsesProdTail_100
-- Once.Parser.TypeRelation.ParsesProdTail
d_ParsesProdTail_100 a0 a1 a2 a3 = ()
data T_ParsesProdTail_100
  = C_ppt'45'done_180 AgdaAny |
    C_ppt'45'star_194 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Type.T_Type_38 T_ParsesAtom_96
                      T_ParsesProdTail_100
-- Once.Parser.TypeRelation.ParsesSum
d_ParsesSum_102 a0 a1 a2 = ()
data T_ParsesSum_102
  = C_ps'45'mk_206 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Type.T_Type_38 T_ParsesProd_98
                   T_ParsesSumTail_104
-- Once.Parser.TypeRelation.ParsesSumTail
d_ParsesSumTail_104 a0 a1 a2 a3 = ()
data T_ParsesSumTail_104
  = C_pst'45'done_212 AgdaAny |
    C_pst'45'plus_226 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Type.T_Type_38 T_ParsesProd_98
                      T_ParsesSumTail_104
-- Once.Parser.TypeRelation.ParsesType
d_ParsesType_106 a0 a1 a2 = ()
data T_ParsesType_106
  = C_pt'45'mk_238 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Type.T_Type_38 T_ParsesSum_102
                   T_ParsesArrowTail_108
-- Once.Parser.TypeRelation.ParsesArrowTail
d_ParsesArrowTail_108 a0 a1 a2 a3 = ()
data T_ParsesArrowTail_108
  = C_pat'45'done_244 AgdaAny |
    C_pat'45'arrow'45'g_256 T_ParsesType_106 |
    C_pat'45'arrow_266 T_ParsesType_106
-- Once.Parser.TypeRelation.ParsesAtom-shrinks
d_ParsesAtom'45'shrinks_274 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAtom_96 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAtom'45'shrinks_274 v0 v1 v2 v3
  = case coe v3 of
      C_pa'45'unit_112
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'void_116
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'int_120
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'float_124
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'buffer_128
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'string_132
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pa'45'eff_144 v5 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_Eff_58 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
                           (coe
                              d_ParsesAtom'45'shrinks_274 (coe v5) (coe v14) (coe v2) (coe v10))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                              (coe
                                 d_ParsesAtom'45'shrinks_274 (coe v12) (coe v13) (coe v5) (coe v9))
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                 (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                       (let v15 = \ v15 -> addInt (coe (1 :: Integer)) (coe v15) in
                                        coe (coe (\ v16 -> v15)))
                                       (coe (0 :: Integer)) (coe v12)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'io_152 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_Eff_58 v10 v11
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                           (coe
                              d_ParsesAtom'45'shrinks_274 (coe v9) (coe v11) (coe v2) (coe v7))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                     coe (coe (\ v13 -> v12)))
                                    (coe (0 :: Integer)) (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'paren_162 v5 v8
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
                          d_ParsesType'45'shrinks_328 (coe v11) (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_16) (coe v2))
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
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesProd-shrinks
d_ParsesProd'45'shrinks_282 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProd_98 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesProd'45'shrinks_282 v0 ~v1 ~v2 v3
  = du_ParsesProd'45'shrinks_282 v0 v3
du_ParsesProd'45'shrinks_282 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProd_98 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesProd'45'shrinks_282 v0 v1
  = case coe v1 of
      C_pp'45'mk_174 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesProdTail'45'shrinks_292 (coe v3) (coe v8))
             (coe
                d_ParsesAtom'45'shrinks_274 (coe v0) (coe v5) (coe v3) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesProdTail-shrinks
d_ParsesProdTail'45'shrinks_292 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdTail_100 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesProdTail'45'shrinks_292 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesProdTail'45'shrinks_292 v1 v4
du_ParsesProdTail'45'shrinks_292 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdTail_100 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesProdTail'45'shrinks_292 v0 v1
  = case coe v1 of
      C_ppt'45'done_180 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_ppt'45'star_194 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesProdTail'45'shrinks_292 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe
                             d_ParsesAtom'45'shrinks_274 (coe v11) (coe v6) (coe v4) (coe v8))
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
d_ParsesSum'45'shrinks_300 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSum_102 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesSum'45'shrinks_300 v0 ~v1 ~v2 v3
  = du_ParsesSum'45'shrinks_300 v0 v3
du_ParsesSum'45'shrinks_300 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSum_102 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesSum'45'shrinks_300 v0 v1
  = case coe v1 of
      C_ps'45'mk_206 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesSumTail'45'shrinks_310 (coe v3) (coe v8))
             (coe du_ParsesProd'45'shrinks_282 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeRelation.ParsesSumTail-shrinks
d_ParsesSumTail'45'shrinks_310 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumTail_104 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesSumTail'45'shrinks_310 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesSumTail'45'shrinks_310 v1 v4
du_ParsesSumTail'45'shrinks_310 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumTail_104 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesSumTail'45'shrinks_310 v0 v1
  = case coe v1 of
      C_pst'45'done_212 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pst'45'plus_226 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesSumTail'45'shrinks_310 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesProd'45'shrinks_282 (coe v11) (coe v8))
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
d_ParsesArrowTail'45'shrinks_320 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesArrowTail_108 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesArrowTail'45'shrinks_320 ~v0 v1 v2 v3 v4
  = du_ParsesArrowTail'45'shrinks_320 v1 v2 v3 v4
du_ParsesArrowTail'45'shrinks_320 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesArrowTail_108 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesArrowTail'45'shrinks_320 v0 v1 v2 v3
  = case coe v3 of
      C_pat'45'done_244 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pat'45'arrow'45'g_256 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v11 of
                    (:) v12 v13
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v14 v15 v16
                             -> coe
                                  seq (coe v15)
                                  (coe
                                     MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                     (coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                        (coe MAlonzo.Code.Data.List.Base.du_length_268 v13)
                                        (coe
                                           d_ParsesType'45'shrinks_328 (coe v13) (coe v16) (coe v2)
                                           (coe v9))
                                        (coe
                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                           (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                 (let v17
                                                        = \ v17 ->
                                                            addInt (coe (1 :: Integer)) (coe v17) in
                                                  coe (coe (\ v18 -> v17)))
                                                 (coe (0 :: Integer)) (coe v13))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pat'45'arrow_266 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v11 v12 v13
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                              (coe
                                 d_ParsesType'45'shrinks_328 (coe v10) (coe v13) (coe v2) (coe v8))
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
d_ParsesType'45'shrinks_328 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesType_106 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesType'45'shrinks_328 v0 v1 v2 v3
  = case coe v3 of
      C_pt'45'mk_238 v5 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe
                du_ParsesArrowTail'45'shrinks_320 (coe v5) (coe v1) (coe v2)
                (coe v10))
             (coe du_ParsesSum'45'shrinks_300 (coe v0) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
