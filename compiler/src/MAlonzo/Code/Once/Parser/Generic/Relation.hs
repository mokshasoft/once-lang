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

module MAlonzo.Code.Once.Parser.Generic.Relation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type

-- Once.Parser.Generic.Relation.isStar
d_isStar_8 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> Bool
d_isStar_8 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TStar_52
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Generic.Relation.isPlus
d_isPlus_10 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> Bool
d_isPlus_10 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TPlus_48
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Generic.Relation.ArrowDir
d_ArrowDir_12 = ()
data T_ArrowDir_12
  = C_adG_14 MAlonzo.Code.Once.Type.T_Quantity_4 | C_adA_16 |
    C_adR_18 | C_adD_20
-- Once.Parser.Generic.Relation.arrowDir
d_arrowDir_22 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_ArrowDir_12
d_arrowDir_22 v0
  = let v1 = coe C_adD_20 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TArrow_28 -> coe C_adA_16
                MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
                  -> let v4 = coe C_adR_18 in
                     coe
                       (case coe v3 of
                          (:) v5 v6
                            -> case coe v5 of
                                 MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                   -> coe C_adG_14 (coe MAlonzo.Code.Once.Type.C_One_8)
                                 _ -> coe v4
                          _ -> coe v4)
                MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
                  -> let v4 = coe C_adR_18 in
                     coe
                       (case coe v3 of
                          (:) v5 v6
                            -> case coe v5 of
                                 MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                   -> coe C_adG_14 (coe MAlonzo.Code.Once.Type.C_Zero_6)
                                 _ -> coe v4
                          _ -> coe v4)
                MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
                  -> let v4 = coe C_adR_18 in
                     coe
                       (case coe v3 of
                          (:) v5 v6
                            -> case coe v5 of
                                 MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                   -> coe C_adG_14 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                 _ -> coe v4
                          _ -> coe v4)
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Generic.Relation.drop1
d_drop1_24 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_drop1_24 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.drop1-≤
d_drop1'45''8804'_30 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop1'45''8804'_30 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268 (d_drop1_24 (coe v0))))
-- Once.Parser.Generic.Relation.drop2
d_drop2_34 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_drop2_34 v0
  = case coe v0 of
      (:) v1 v2
        -> case coe v2 of
             (:) v3 v4 -> coe v4
             _ -> coe v0
      _ -> coe v0
-- Once.Parser.Generic.Relation.drop2-≤
d_drop2'45''8804'_42 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop2'45''8804'_42 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe
                MAlonzo.Code.Data.List.Base.du_length_268 (d_drop2_34 (coe v0)))
      (:) v1 v2
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_length_268 (d_drop2_34 (coe v0))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg
d_TyAlg_46 = ()
data T_TyAlg_46
  = C_constructor_244 AgdaAny AgdaAny AgdaAny AgdaAny
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
                      (MAlonzo.Code.Once.Type.T_Quantity_4 ->
                       AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny) AgdaAny (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
                      ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
                       AgdaAny ->
                       [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
                       AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
                       Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Parser.Generic.Relation.TyAlg.R
d_R_146 :: T_TyAlg_46 -> ()
d_R_146 = erased
-- Once.Parser.Generic.Relation.TyAlg.RF
d_RF_148 :: T_TyAlg_46 -> ()
d_RF_148 = erased
-- Once.Parser.Generic.Relation.TyAlg.aUnit
d_aUnit_150 :: T_TyAlg_46 -> AgdaAny
d_aUnit_150 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aVoid
d_aVoid_152 :: T_TyAlg_46 -> AgdaAny
d_aVoid_152 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aInt
d_aInt_154 :: T_TyAlg_46 -> AgdaAny
d_aInt_154 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aFloat
d_aFloat_156 :: T_TyAlg_46 -> AgdaAny
d_aFloat_156 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aProd
d_aProd_158 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aProd_158 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aSum
d_aSum_160 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aSum_160 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aEff
d_aEff_162 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aEff_162 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aArrow
d_aArrow_164 ::
  T_TyAlg_46 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_aArrow_164 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aMu
d_aMu_166 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aMu_166 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aNu
d_aNu_168 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aNu_168 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aNuEff
d_aNuEff_170 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aNuEff_170 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.fK
d_fK_172 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_fK_172 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.fId
d_fId_174 :: T_TyAlg_46 -> AgdaAny
d_fId_174 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.fSum
d_fSum_176 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_fSum_176 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.fProd
d_fProd_178 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_fProd_178 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.Extra
d_Extra_180 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_Extra_180 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraShrink
d_extraShrink_188 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_extraShrink_188 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v19
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.extraP
d_extraP_196 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extraP_196 v0
  = case coe v0 of
      C_constructor_244 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20
        -> coe v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.extraComplete
d_extraComplete_206 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraComplete_206 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Unit
d_extraMiss'45'Unit_210 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Unit_210 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Void
d_extraMiss'45'Void_214 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Void_214 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Int
d_extraMiss'45'Int_218 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Int_218 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Float
d_extraMiss'45'Float_222 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Float_222 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Eff
d_extraMiss'45'Eff_226 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Eff_226 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-IO
d_extraMiss'45'IO_230 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'IO_230 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Mu
d_extraMiss'45'Mu_234 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Mu_234 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Nu
d_extraMiss'45'Nu_238 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Nu_238 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-LParen
d_extraMiss'45'LParen_242 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'LParen_242 = erased
-- Once.Parser.Generic.Relation.isStar-<
d_isStar'45''60'_248 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_isStar'45''60'_248 v0 ~v1 = du_isStar'45''60'_248 v0
du_isStar'45''60'_248 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_isStar'45''60'_248 v0
  = case coe v0 of
      (:) v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (let v3 = \ v3 -> addInt (coe (1 :: Integer)) (coe v3) in
                       coe (coe (\ v4 -> v3)))
                      (coe (0 :: Integer)) (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.isPlus-<
d_isPlus'45''60'_256 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_isPlus'45''60'_256 v0 ~v1 = du_isPlus'45''60'_256 v0
du_isPlus'45''60'_256 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_isPlus'45''60'_256 v0
  = case coe v0 of
      (:) v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (let v3 = \ v3 -> addInt (coe (1 :: Integer)) (coe v3) in
                       coe (coe (\ v4 -> v3)))
                      (coe (0 :: Integer)) (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.arrowDir-A-<
d_arrowDir'45'A'45''60'_264 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowDir'45'A'45''60'_264 v0 ~v1
  = du_arrowDir'45'A'45''60'_264 v0
du_arrowDir'45'A'45''60'_264 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_arrowDir'45'A'45''60'_264 v0
  = case coe v0 of
      (:) v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (let v3 = \ v3 -> addInt (coe (1 :: Integer)) (coe v3) in
                       coe (coe (\ v4 -> v3)))
                      (coe (0 :: Integer)) (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.arrowDir-G-<
d_arrowDir'45'G'45''60'_274 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowDir'45'G'45''60'_274 v0 ~v1 ~v2
  = du_arrowDir'45'G'45''60'_274 v0
du_arrowDir'45'G'45''60'_274 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_arrowDir'45'G'45''60'_274 v0
  = case coe v0 of
      (:) v1 v2
        -> coe
             seq (coe v1)
             (case coe v2 of
                (:) v3 v4
                  -> coe
                       seq (coe v3)
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                                 coe (coe (\ v6 -> v5)))
                                (coe (0 :: Integer)) (coe v4))))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen._.Extra
d_Extra_294 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_Extra_294 = erased
-- Once.Parser.Generic.Relation.Gen._.R
d_R_296 :: T_TyAlg_46 -> ()
d_R_296 = erased
-- Once.Parser.Generic.Relation.Gen._.RF
d_RF_298 :: T_TyAlg_46 -> ()
d_RF_298 = erased
-- Once.Parser.Generic.Relation.Gen._.aArrow
d_aArrow_300 ::
  T_TyAlg_46 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_aArrow_300 v0 = coe d_aArrow_164 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aEff
d_aEff_302 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aEff_302 v0 = coe d_aEff_162 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aFloat
d_aFloat_304 :: T_TyAlg_46 -> AgdaAny
d_aFloat_304 v0 = coe d_aFloat_156 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aInt
d_aInt_306 :: T_TyAlg_46 -> AgdaAny
d_aInt_306 v0 = coe d_aInt_154 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aMu
d_aMu_308 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aMu_308 v0 = coe d_aMu_166 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aNu
d_aNu_310 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aNu_310 v0 = coe d_aNu_168 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aNuEff
d_aNuEff_312 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aNuEff_312 v0 = coe d_aNuEff_170 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aProd
d_aProd_314 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aProd_314 v0 = coe d_aProd_158 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aSum
d_aSum_316 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aSum_316 v0 = coe d_aSum_160 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aUnit
d_aUnit_318 :: T_TyAlg_46 -> AgdaAny
d_aUnit_318 v0 = coe d_aUnit_150 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aVoid
d_aVoid_320 :: T_TyAlg_46 -> AgdaAny
d_aVoid_320 v0 = coe d_aVoid_152 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.extraComplete
d_extraComplete_322 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraComplete_322 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Eff
d_extraMiss'45'Eff_324 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Eff_324 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Float
d_extraMiss'45'Float_326 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Float_326 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-IO
d_extraMiss'45'IO_328 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'IO_328 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Int
d_extraMiss'45'Int_330 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Int_330 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-LParen
d_extraMiss'45'LParen_332 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'LParen_332 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Mu
d_extraMiss'45'Mu_334 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Mu_334 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Nu
d_extraMiss'45'Nu_336 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Nu_336 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Unit
d_extraMiss'45'Unit_338 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Unit_338 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Void
d_extraMiss'45'Void_340 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Void_340 = erased
-- Once.Parser.Generic.Relation.Gen._.extraP
d_extraP_342 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extraP_342 v0 = coe d_extraP_196 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.extraShrink
d_extraShrink_344 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_extraShrink_344 v0 = coe d_extraShrink_188 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.fId
d_fId_346 :: T_TyAlg_46 -> AgdaAny
d_fId_346 v0 = coe d_fId_174 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.fK
d_fK_348 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_fK_348 v0 = coe d_fK_172 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.fProd
d_fProd_350 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_fProd_350 v0 = coe d_fProd_178 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.fSum
d_fSum_352 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_fSum_352 v0 = coe d_fSum_176 (coe v0)
-- Once.Parser.Generic.Relation.Gen.ParsesAtomG
d_ParsesAtomG_354 a0 a1 a2 a3 = ()
data T_ParsesAtomG_354
  = C_pa'45'unit_380 | C_pa'45'void_384 | C_pa'45'int_388 |
    C_pa'45'float_392 |
    C_pa'45'eff_404 [MAlonzo.Code.Once.Parser.Token.T_Token_6] AgdaAny
                    AgdaAny T_ParsesAtomG_354 T_ParsesAtomG_354 |
    C_pa'45'io_412 AgdaAny T_ParsesAtomG_354 |
    C_pa'45'mu_420 AgdaAny T_ParsesFuncSumG_374 |
    C_pa'45'nu_428 AgdaAny T_ParsesFuncSumG_374 |
    C_pa'45'nu'45'eff_436 AgdaAny T_ParsesFuncSumG_374 |
    C_pa'45'extra_444 AgdaAny |
    C_pa'45'paren_454 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      T_ParsesTypeG_364
-- Once.Parser.Generic.Relation.Gen.ParsesProdG
d_ParsesProdG_356 a0 a1 a2 a3 = ()
data T_ParsesProdG_356
  = C_pp'45'mk_466 [MAlonzo.Code.Once.Parser.Token.T_Token_6] AgdaAny
                   T_ParsesAtomG_354 T_ParsesProdTailG_358
-- Once.Parser.Generic.Relation.Gen.ParsesProdTailG
d_ParsesProdTailG_358 a0 a1 a2 a3 a4 = ()
data T_ParsesProdTailG_358
  = C_ppt'45'done_472 |
    C_ppt'45'star_486 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      AgdaAny T_ParsesAtomG_354 T_ParsesProdTailG_358
-- Once.Parser.Generic.Relation.Gen.ParsesSumG
d_ParsesSumG_360 a0 a1 a2 a3 = ()
data T_ParsesSumG_360
  = C_ps'45'mk_498 [MAlonzo.Code.Once.Parser.Token.T_Token_6] AgdaAny
                   T_ParsesProdG_356 T_ParsesSumTailG_362
-- Once.Parser.Generic.Relation.Gen.ParsesSumTailG
d_ParsesSumTailG_362 a0 a1 a2 a3 a4 = ()
data T_ParsesSumTailG_362
  = C_pst'45'done_504 |
    C_pst'45'plus_518 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      AgdaAny T_ParsesProdG_356 T_ParsesSumTailG_362
-- Once.Parser.Generic.Relation.Gen.ParsesTypeG
d_ParsesTypeG_364 a0 a1 a2 a3 = ()
data T_ParsesTypeG_364
  = C_pt'45'mk_530 [MAlonzo.Code.Once.Parser.Token.T_Token_6] AgdaAny
                   T_ParsesSumG_360 T_ParsesArrowTailG_366
-- Once.Parser.Generic.Relation.Gen.ParsesArrowTailG
d_ParsesArrowTailG_366 a0 a1 a2 a3 a4 = ()
data T_ParsesArrowTailG_366
  = C_pat'45'done_536 |
    C_pat'45'arrow'45'g_548 AgdaAny MAlonzo.Code.Once.Type.T_Quantity_4
                            T_ParsesTypeG_364 |
    C_pat'45'arrow_558 AgdaAny T_ParsesTypeG_364
-- Once.Parser.Generic.Relation.Gen.ParsesFuncAtomG
d_ParsesFuncAtomG_368 a0 a1 a2 a3 = ()
data T_ParsesFuncAtomG_368
  = C_pfa'45'id_562 | C_pfa'45'k_570 AgdaAny T_ParsesAtomG_354 |
    C_pfa'45'paren_580 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       T_ParsesFuncSumG_374
-- Once.Parser.Generic.Relation.Gen.ParsesFuncProdG
d_ParsesFuncProdG_370 a0 a1 a2 a3 = ()
data T_ParsesFuncProdG_370
  = C_pfp'45'mk_592 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    AgdaAny T_ParsesFuncAtomG_368 T_ParsesFuncProdTailG_372
-- Once.Parser.Generic.Relation.Gen.ParsesFuncProdTailG
d_ParsesFuncProdTailG_372 a0 a1 a2 a3 a4 = ()
data T_ParsesFuncProdTailG_372
  = C_pfpt'45'done_598 |
    C_pfpt'45'star_612 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       AgdaAny T_ParsesFuncAtomG_368 T_ParsesFuncProdTailG_372
-- Once.Parser.Generic.Relation.Gen.ParsesFuncSumG
d_ParsesFuncSumG_374 a0 a1 a2 a3 = ()
data T_ParsesFuncSumG_374
  = C_pfs'45'mk_624 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    AgdaAny T_ParsesFuncProdG_370 T_ParsesFuncSumTailG_376
-- Once.Parser.Generic.Relation.Gen.ParsesFuncSumTailG
d_ParsesFuncSumTailG_376 a0 a1 a2 a3 a4 = ()
data T_ParsesFuncSumTailG_376
  = C_pfst'45'done_630 |
    C_pfst'45'plus_644 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       AgdaAny T_ParsesFuncProdG_370 T_ParsesFuncSumTailG_376
-- Once.Parser.Generic.Relation.Gen.atomShrink
d_atomShrink_652 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAtomG_354 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_atomShrink_652 v0 v1 v2 v3 v4
  = case coe v4 of
      C_pa'45'unit_380
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v3)))
      C_pa'45'void_384
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v3)))
      C_pa'45'int_388
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v3)))
      C_pa'45'float_392
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v3)))
      C_pa'45'eff_404 v6 v8 v9 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                    (coe
                       d_atomShrink_652 (coe v0) (coe v6) (coe v9) (coe v3) (coe v11))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v13)
                       (coe
                          d_atomShrink_652 (coe v0) (coe v13) (coe v8) (coe v6) (coe v10))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v14 = \ v14 -> addInt (coe (1 :: Integer)) (coe v14) in
                                 coe (coe (\ v15 -> v14)))
                                (coe (0 :: Integer)) (coe v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'io_412 v7 v8
        -> case coe v1 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                    (coe
                       d_atomShrink_652 (coe v0) (coe v10) (coe v7) (coe v3) (coe v8))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v11 = \ v11 -> addInt (coe (1 :: Integer)) (coe v11) in
                              coe (coe (\ v12 -> v11)))
                             (coe (0 :: Integer)) (coe v10))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'mu_420 v7 v8
        -> case coe v1 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                    (coe du_funcSumShrink_740 (coe v0) (coe v10) (coe v8))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v11 = \ v11 -> addInt (coe (1 :: Integer)) (coe v11) in
                              coe (coe (\ v12 -> v11)))
                             (coe (0 :: Integer)) (coe v10))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'nu_428 v7 v8
        -> case coe v1 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                    (coe du_funcSumShrink_740 (coe v0) (coe v10) (coe v8))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v11 = \ v11 -> addInt (coe (1 :: Integer)) (coe v11) in
                              coe (coe (\ v12 -> v11)))
                             (coe (0 :: Integer)) (coe v10))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'nu'45'eff_436 v7 v8
        -> case coe v1 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> case coe v12 of
                           (:) v13 v14
                             -> coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                  (coe
                                     addInt (coe (2 :: Integer))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                        (let v15 = \ v15 -> addInt (coe (1 :: Integer)) (coe v15) in
                                         coe (coe (\ v16 -> v15)))
                                        (coe (0 :: Integer)) (coe v14)))
                                  (coe
                                     MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                     (coe
                                        addInt (coe (1 :: Integer))
                                        (coe
                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                           (let v15
                                                  = \ v15 ->
                                                      addInt (coe (1 :: Integer)) (coe v15) in
                                            coe (coe (\ v16 -> v15)))
                                           (coe (0 :: Integer)) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                        (coe MAlonzo.Code.Data.List.Base.du_length_268 v14)
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                 (coe
                                                    (\ v15 v16 ->
                                                       addInt (coe (1 :: Integer)) (coe v16)))
                                                 (coe (0 :: Integer)) (coe v3)))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                 (coe
                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                    (coe
                                                       (\ v15 v16 ->
                                                          addInt (coe (1 :: Integer)) (coe v16)))
                                                    (coe (0 :: Integer)) (coe v3))))
                                           (coe du_funcSumShrink_740 (coe v0) (coe v14) (coe v8)))
                                        (coe
                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                 (let v15
                                                        = \ v15 ->
                                                            addInt (coe (1 :: Integer)) (coe v15) in
                                                  coe (coe (\ v16 -> v15)))
                                                 (coe (0 :: Integer)) (coe v14)))))
                                     (coe
                                        MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                        (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                 (let v15
                                                        = \ v15 ->
                                                            addInt (coe (1 :: Integer)) (coe v15) in
                                                  coe (coe (\ v16 -> v15)))
                                                 (coe (0 :: Integer)) (coe v14))))))
                                  (coe
                                     MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                     (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                        (coe
                                           addInt (coe (2 :: Integer))
                                           (coe
                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                              (let v15
                                                     = \ v15 ->
                                                         addInt (coe (1 :: Integer)) (coe v15) in
                                               coe (coe (\ v16 -> v15)))
                                              (coe (0 :: Integer)) (coe v14)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'extra_444 v8 -> coe d_extraShrink_188 v0 v1 v2 v3 v8
      C_pa'45'paren_454 v6 v9
        -> case coe v1 of
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_foldr_216
                          (coe (\ v13 v14 -> addInt (coe (1 :: Integer)) (coe v14)))
                          (coe (0 :: Integer)) (coe v3)))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (coe (\ v13 v14 -> addInt (coe (1 :: Integer)) (coe v14)))
                             (coe (0 :: Integer)) (coe v3))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                       (coe
                          du_typeShrink_706 (coe v0) (coe v12)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v3))
                          (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                 coe (coe (\ v14 -> v13)))
                                (coe (0 :: Integer)) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.prodShrink
d_prodShrink_660 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdG_356 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodShrink_660 v0 v1 ~v2 ~v3 v4 = du_prodShrink_660 v0 v1 v4
du_prodShrink_660 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdG_356 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_prodShrink_660 v0 v1 v2
  = case coe v2 of
      C_pp'45'mk_466 v4 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_prodTailShrink_670 (coe v0) (coe v4) (coe v9))
             (coe d_atomShrink_652 (coe v0) (coe v1) (coe v6) (coe v4) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.prodTailShrink
d_prodTailShrink_670 ::
  T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdTailG_358 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodTailShrink_670 v0 ~v1 v2 ~v3 ~v4 v5
  = du_prodTailShrink_670 v0 v2 v5
du_prodTailShrink_670 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdTailG_358 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_prodTailShrink_670 v0 v1 v2
  = case coe v2 of
      C_ppt'45'done_472
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      C_ppt'45'star_486 v5 v7 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                (coe du_prodTailShrink_670 (coe v0) (coe v5) (coe v11))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                   (coe
                      d_atomShrink_652 (coe v0) (coe d_drop1_24 (coe v1)) (coe v7)
                      (coe v5) (coe v10))
                   (coe d_drop1'45''8804'_30 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.sumShrink
d_sumShrink_678 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumG_360 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumShrink_678 v0 v1 ~v2 ~v3 v4 = du_sumShrink_678 v0 v1 v4
du_sumShrink_678 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumG_360 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sumShrink_678 v0 v1 v2
  = case coe v2 of
      C_ps'45'mk_498 v4 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_sumTailShrink_688 (coe v0) (coe v4) (coe v9))
             (coe du_prodShrink_660 (coe v0) (coe v1) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.sumTailShrink
d_sumTailShrink_688 ::
  T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumTailG_362 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumTailShrink_688 v0 ~v1 v2 ~v3 ~v4 v5
  = du_sumTailShrink_688 v0 v2 v5
du_sumTailShrink_688 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumTailG_362 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sumTailShrink_688 v0 v1 v2
  = case coe v2 of
      C_pst'45'done_504
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      C_pst'45'plus_518 v5 v7 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                (coe du_sumTailShrink_688 (coe v0) (coe v5) (coe v11))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                   (coe
                      du_prodShrink_660 (coe v0) (coe d_drop1_24 (coe v1)) (coe v10))
                   (coe d_drop1'45''8804'_30 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.arrowTailShrink
d_arrowTailShrink_698 ::
  T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesArrowTailG_366 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowTailShrink_698 v0 ~v1 v2 ~v3 v4 v5
  = du_arrowTailShrink_698 v0 v2 v4 v5
du_arrowTailShrink_698 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesArrowTailG_366 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_arrowTailShrink_698 v0 v1 v2 v3
  = case coe v3 of
      C_pat'45'done_536
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      C_pat'45'arrow'45'g_548 v7 v8 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe
                   du_typeShrink_706 (coe v0) (coe d_drop2_34 (coe v1)) (coe v2)
                   (coe v10))
                (coe d_drop2'45''8804'_42 (coe v1)))
      C_pat'45'arrow_558 v7 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe
                   du_typeShrink_706 (coe v0) (coe d_drop1_24 (coe v1)) (coe v2)
                   (coe v9))
                (coe d_drop1'45''8804'_30 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.typeShrink
d_typeShrink_706 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesTypeG_364 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_typeShrink_706 v0 v1 ~v2 v3 v4 = du_typeShrink_706 v0 v1 v3 v4
du_typeShrink_706 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesTypeG_364 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_typeShrink_706 v0 v1 v2 v3
  = case coe v3 of
      C_pt'45'mk_530 v5 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_arrowTailShrink_698 (coe v0) (coe v5) (coe v2) (coe v10))
             (coe du_sumShrink_678 (coe v0) (coe v1) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.funcAtomShrink
d_funcAtomShrink_714 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncAtomG_368 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcAtomShrink_714 v0 v1 v2 v3 v4
  = case coe v4 of
      C_pfa'45'id_562
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v3)))
      C_pfa'45'k_570 v7 v8
        -> case coe v1 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                    (coe
                       d_atomShrink_652 (coe v0) (coe v10) (coe v7) (coe v3) (coe v8))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v11 = \ v11 -> addInt (coe (1 :: Integer)) (coe v11) in
                              coe (coe (\ v12 -> v11)))
                             (coe (0 :: Integer)) (coe v10))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pfa'45'paren_580 v6 v9
        -> case coe v1 of
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_foldr_216
                          (coe (\ v13 v14 -> addInt (coe (1 :: Integer)) (coe v14)))
                          (coe (0 :: Integer)) (coe v3)))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (coe (\ v13 v14 -> addInt (coe (1 :: Integer)) (coe v14)))
                             (coe (0 :: Integer)) (coe v3))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                       (coe du_funcSumShrink_740 (coe v0) (coe v12) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                 coe (coe (\ v14 -> v13)))
                                (coe (0 :: Integer)) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.funcProdShrink
d_funcProdShrink_722 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncProdG_370 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdShrink_722 v0 v1 ~v2 ~v3 v4
  = du_funcProdShrink_722 v0 v1 v4
du_funcProdShrink_722 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncProdG_370 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_funcProdShrink_722 v0 v1 v2
  = case coe v2 of
      C_pfp'45'mk_592 v4 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_funcProdTailShrink_732 (coe v0) (coe v4) (coe v9))
             (coe
                d_funcAtomShrink_714 (coe v0) (coe v1) (coe v6) (coe v4) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.funcProdTailShrink
d_funcProdTailShrink_732 ::
  T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncProdTailG_372 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdTailShrink_732 v0 ~v1 v2 ~v3 ~v4 v5
  = du_funcProdTailShrink_732 v0 v2 v5
du_funcProdTailShrink_732 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncProdTailG_372 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_funcProdTailShrink_732 v0 v1 v2
  = case coe v2 of
      C_pfpt'45'done_598
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      C_pfpt'45'star_612 v5 v7 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                (coe du_funcProdTailShrink_732 (coe v0) (coe v5) (coe v11))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                   (coe
                      d_funcAtomShrink_714 (coe v0) (coe d_drop1_24 (coe v1)) (coe v7)
                      (coe v5) (coe v10))
                   (coe d_drop1'45''8804'_30 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.funcSumShrink
d_funcSumShrink_740 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncSumG_374 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumShrink_740 v0 v1 ~v2 ~v3 v4
  = du_funcSumShrink_740 v0 v1 v4
du_funcSumShrink_740 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncSumG_374 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_funcSumShrink_740 v0 v1 v2
  = case coe v2 of
      C_pfs'45'mk_624 v4 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_funcSumTailShrink_750 (coe v0) (coe v4) (coe v9))
             (coe du_funcProdShrink_722 (coe v0) (coe v1) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.funcSumTailShrink
d_funcSumTailShrink_750 ::
  T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncSumTailG_376 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumTailShrink_750 v0 ~v1 v2 ~v3 ~v4 v5
  = du_funcSumTailShrink_750 v0 v2 v5
du_funcSumTailShrink_750 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncSumTailG_376 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_funcSumTailShrink_750 v0 v1 v2
  = case coe v2 of
      C_pfst'45'done_630
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      C_pfst'45'plus_644 v5 v7 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                (coe du_funcSumTailShrink_750 (coe v0) (coe v5) (coe v11))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                   (coe
                      du_funcProdShrink_722 (coe v0) (coe d_drop1_24 (coe v1)) (coe v10))
                   (coe d_drop1'45''8804'_30 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
