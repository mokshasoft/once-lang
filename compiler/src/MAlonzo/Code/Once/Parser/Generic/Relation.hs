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
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Parser.Token

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
  = C_adG_14 MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 |
    C_adA_16 | C_adR_18 | C_adD_20
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
                                   -> coe C_adG_14 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                                 _ -> coe v4
                          _ -> coe v4)
                MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
                  -> let v4 = coe C_adR_18 in
                     coe
                       (case coe v3 of
                          (:) v5 v6
                            -> case coe v5 of
                                 MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                   -> coe C_adG_14 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                                 _ -> coe v4
                          _ -> coe v4)
                MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
                  -> let v4 = coe C_adR_18 in
                     coe
                       (case coe v3 of
                          (:) v5 v6
                            -> case coe v5 of
                                 MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                   -> coe C_adG_14 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
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
  = C_constructor_252 AgdaAny AgdaAny AgdaAny AgdaAny
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                      (MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
                       AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) AgdaAny
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                      ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
                       AgdaAny ->
                       [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
                       AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
                       Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Parser.Generic.Relation.TyAlg.R
d_R_150 :: T_TyAlg_46 -> ()
d_R_150 = erased
-- Once.Parser.Generic.Relation.TyAlg.RF
d_RF_152 :: T_TyAlg_46 -> ()
d_RF_152 = erased
-- Once.Parser.Generic.Relation.TyAlg.aUnit
d_aUnit_154 :: T_TyAlg_46 -> AgdaAny
d_aUnit_154 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aVoid
d_aVoid_156 :: T_TyAlg_46 -> AgdaAny
d_aVoid_156 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aInt
d_aInt_158 :: T_TyAlg_46 -> AgdaAny
d_aInt_158 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aFloat
d_aFloat_160 :: T_TyAlg_46 -> AgdaAny
d_aFloat_160 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aProd
d_aProd_162 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aProd_162 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aSum
d_aSum_164 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aSum_164 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aEff
d_aEff_166 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aEff_166 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aAct
d_aAct_168 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aAct_168 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aArrow
d_aArrow_170 ::
  T_TyAlg_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_aArrow_170 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aMu
d_aMu_172 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aMu_172 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aNu
d_aNu_174 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aNu_174 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aNuEff
d_aNuEff_176 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aNuEff_176 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.aNuAct
d_aNuAct_178 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aNuAct_178 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.fK
d_fK_180 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_fK_180 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.fId
d_fId_182 :: T_TyAlg_46 -> AgdaAny
d_fId_182 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.fSum
d_fSum_184 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_fSum_184 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.fProd
d_fProd_186 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_fProd_186 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v19
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.Extra
d_Extra_188 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_Extra_188 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraShrink
d_extraShrink_196 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_extraShrink_196 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v21
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.extraP
d_extraP_204 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extraP_204 v0
  = case coe v0 of
      C_constructor_252 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 v22
        -> coe v22
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.TyAlg.extraComplete
d_extraComplete_214 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraComplete_214 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Unit
d_extraMiss'45'Unit_218 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Unit_218 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Void
d_extraMiss'45'Void_222 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Void_222 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Int
d_extraMiss'45'Int_226 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Int_226 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Float
d_extraMiss'45'Float_230 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Float_230 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Eff
d_extraMiss'45'Eff_234 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Eff_234 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Act
d_extraMiss'45'Act_238 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Act_238 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Mu
d_extraMiss'45'Mu_242 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Mu_242 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-Nu
d_extraMiss'45'Nu_246 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Nu_246 = erased
-- Once.Parser.Generic.Relation.TyAlg.extraMiss-LParen
d_extraMiss'45'LParen_250 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'LParen_250 = erased
-- Once.Parser.Generic.Relation.isStar-<
d_isStar'45''60'_256 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_isStar'45''60'_256 v0 ~v1 = du_isStar'45''60'_256 v0
du_isStar'45''60'_256 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_isStar'45''60'_256 v0
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
d_isPlus'45''60'_264 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_isPlus'45''60'_264 v0 ~v1 = du_isPlus'45''60'_264 v0
du_isPlus'45''60'_264 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_isPlus'45''60'_264 v0
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
d_arrowDir'45'A'45''60'_272 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowDir'45'A'45''60'_272 v0 ~v1
  = du_arrowDir'45'A'45''60'_272 v0
du_arrowDir'45'A'45''60'_272 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_arrowDir'45'A'45''60'_272 v0
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
d_arrowDir'45'G'45''60'_282 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowDir'45'G'45''60'_282 v0 ~v1 ~v2
  = du_arrowDir'45'G'45''60'_282 v0
du_arrowDir'45'G'45''60'_282 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_arrowDir'45'G'45''60'_282 v0
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
d_Extra_302 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_Extra_302 = erased
-- Once.Parser.Generic.Relation.Gen._.R
d_R_304 :: T_TyAlg_46 -> ()
d_R_304 = erased
-- Once.Parser.Generic.Relation.Gen._.RF
d_RF_306 :: T_TyAlg_46 -> ()
d_RF_306 = erased
-- Once.Parser.Generic.Relation.Gen._.aAct
d_aAct_308 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aAct_308 v0 = coe d_aAct_168 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aArrow
d_aArrow_310 ::
  T_TyAlg_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_aArrow_310 v0 = coe d_aArrow_170 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aEff
d_aEff_312 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aEff_312 v0 = coe d_aEff_166 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aFloat
d_aFloat_314 :: T_TyAlg_46 -> AgdaAny
d_aFloat_314 v0 = coe d_aFloat_160 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aInt
d_aInt_316 :: T_TyAlg_46 -> AgdaAny
d_aInt_316 v0 = coe d_aInt_158 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aMu
d_aMu_318 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aMu_318 v0 = coe d_aMu_172 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aNu
d_aNu_320 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aNu_320 v0 = coe d_aNu_174 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aNuAct
d_aNuAct_322 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aNuAct_322 v0 = coe d_aNuAct_178 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aNuEff
d_aNuEff_324 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_aNuEff_324 v0 = coe d_aNuEff_176 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aProd
d_aProd_326 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aProd_326 v0 = coe d_aProd_162 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aSum
d_aSum_328 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_aSum_328 v0 = coe d_aSum_164 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aUnit
d_aUnit_330 :: T_TyAlg_46 -> AgdaAny
d_aUnit_330 v0 = coe d_aUnit_154 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.aVoid
d_aVoid_332 :: T_TyAlg_46 -> AgdaAny
d_aVoid_332 v0 = coe d_aVoid_156 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.extraComplete
d_extraComplete_334 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraComplete_334 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Act
d_extraMiss'45'Act_336 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Act_336 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Eff
d_extraMiss'45'Eff_338 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Eff_338 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Float
d_extraMiss'45'Float_340 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Float_340 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Int
d_extraMiss'45'Int_342 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Int_342 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-LParen
d_extraMiss'45'LParen_344 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'LParen_344 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Mu
d_extraMiss'45'Mu_346 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Mu_346 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Nu
d_extraMiss'45'Nu_348 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Nu_348 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Unit
d_extraMiss'45'Unit_350 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Unit_350 = erased
-- Once.Parser.Generic.Relation.Gen._.extraMiss-Void
d_extraMiss'45'Void_352 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extraMiss'45'Void_352 = erased
-- Once.Parser.Generic.Relation.Gen._.extraP
d_extraP_354 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extraP_354 v0 = coe d_extraP_204 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.extraShrink
d_extraShrink_356 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_extraShrink_356 v0 = coe d_extraShrink_196 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.fId
d_fId_358 :: T_TyAlg_46 -> AgdaAny
d_fId_358 v0 = coe d_fId_182 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.fK
d_fK_360 :: T_TyAlg_46 -> AgdaAny -> AgdaAny
d_fK_360 v0 = coe d_fK_180 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.fProd
d_fProd_362 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_fProd_362 v0 = coe d_fProd_186 (coe v0)
-- Once.Parser.Generic.Relation.Gen._.fSum
d_fSum_364 :: T_TyAlg_46 -> AgdaAny -> AgdaAny -> AgdaAny
d_fSum_364 v0 = coe d_fSum_184 (coe v0)
-- Once.Parser.Generic.Relation.Gen.ParsesAtomG
d_ParsesAtomG_366 a0 a1 a2 a3 = ()
data T_ParsesAtomG_366
  = C_pa'45'unit_392 | C_pa'45'void_396 | C_pa'45'int_400 |
    C_pa'45'float_404 |
    C_pa'45'eff_416 [MAlonzo.Code.Once.Parser.Token.T_Token_6] AgdaAny
                    AgdaAny T_ParsesAtomG_366 T_ParsesAtomG_366 |
    C_pa'45'act_428 [MAlonzo.Code.Once.Parser.Token.T_Token_6] AgdaAny
                    AgdaAny T_ParsesAtomG_366 T_ParsesAtomG_366 |
    C_pa'45'mu_436 AgdaAny T_ParsesFuncSumG_386 |
    C_pa'45'nu_444 AgdaAny T_ParsesFuncSumG_386 |
    C_pa'45'nu'45'eff_452 AgdaAny T_ParsesFuncSumG_386 |
    C_pa'45'nu'45'act_460 AgdaAny T_ParsesFuncSumG_386 |
    C_pa'45'extra_468 AgdaAny |
    C_pa'45'paren_478 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      T_ParsesTypeG_376
-- Once.Parser.Generic.Relation.Gen.ParsesProdG
d_ParsesProdG_368 a0 a1 a2 a3 = ()
data T_ParsesProdG_368
  = C_pp'45'mk_490 [MAlonzo.Code.Once.Parser.Token.T_Token_6] AgdaAny
                   T_ParsesAtomG_366 T_ParsesProdTailG_370
-- Once.Parser.Generic.Relation.Gen.ParsesProdTailG
d_ParsesProdTailG_370 a0 a1 a2 a3 a4 = ()
data T_ParsesProdTailG_370
  = C_ppt'45'done_496 |
    C_ppt'45'star_510 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      AgdaAny T_ParsesAtomG_366 T_ParsesProdTailG_370
-- Once.Parser.Generic.Relation.Gen.ParsesSumG
d_ParsesSumG_372 a0 a1 a2 a3 = ()
data T_ParsesSumG_372
  = C_ps'45'mk_522 [MAlonzo.Code.Once.Parser.Token.T_Token_6] AgdaAny
                   T_ParsesProdG_368 T_ParsesSumTailG_374
-- Once.Parser.Generic.Relation.Gen.ParsesSumTailG
d_ParsesSumTailG_374 a0 a1 a2 a3 a4 = ()
data T_ParsesSumTailG_374
  = C_pst'45'done_528 |
    C_pst'45'plus_542 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      AgdaAny T_ParsesProdG_368 T_ParsesSumTailG_374
-- Once.Parser.Generic.Relation.Gen.ParsesTypeG
d_ParsesTypeG_376 a0 a1 a2 a3 = ()
data T_ParsesTypeG_376
  = C_pt'45'mk_554 [MAlonzo.Code.Once.Parser.Token.T_Token_6] AgdaAny
                   T_ParsesSumG_372 T_ParsesArrowTailG_378
-- Once.Parser.Generic.Relation.Gen.ParsesArrowTailG
d_ParsesArrowTailG_378 a0 a1 a2 a3 a4 = ()
data T_ParsesArrowTailG_378
  = C_pat'45'done_560 |
    C_pat'45'arrow'45'g_572 AgdaAny
                            MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 T_ParsesTypeG_376 |
    C_pat'45'arrow_582 AgdaAny T_ParsesTypeG_376
-- Once.Parser.Generic.Relation.Gen.ParsesFuncAtomG
d_ParsesFuncAtomG_380 a0 a1 a2 a3 = ()
data T_ParsesFuncAtomG_380
  = C_pfa'45'id_586 | C_pfa'45'k_594 AgdaAny T_ParsesAtomG_366 |
    C_pfa'45'paren_604 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       T_ParsesFuncSumG_386
-- Once.Parser.Generic.Relation.Gen.ParsesFuncProdG
d_ParsesFuncProdG_382 a0 a1 a2 a3 = ()
data T_ParsesFuncProdG_382
  = C_pfp'45'mk_616 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    AgdaAny T_ParsesFuncAtomG_380 T_ParsesFuncProdTailG_384
-- Once.Parser.Generic.Relation.Gen.ParsesFuncProdTailG
d_ParsesFuncProdTailG_384 a0 a1 a2 a3 a4 = ()
data T_ParsesFuncProdTailG_384
  = C_pfpt'45'done_622 |
    C_pfpt'45'star_636 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       AgdaAny T_ParsesFuncAtomG_380 T_ParsesFuncProdTailG_384
-- Once.Parser.Generic.Relation.Gen.ParsesFuncSumG
d_ParsesFuncSumG_386 a0 a1 a2 a3 = ()
data T_ParsesFuncSumG_386
  = C_pfs'45'mk_648 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    AgdaAny T_ParsesFuncProdG_382 T_ParsesFuncSumTailG_388
-- Once.Parser.Generic.Relation.Gen.ParsesFuncSumTailG
d_ParsesFuncSumTailG_388 a0 a1 a2 a3 a4 = ()
data T_ParsesFuncSumTailG_388
  = C_pfst'45'done_654 |
    C_pfst'45'plus_668 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       AgdaAny T_ParsesFuncProdG_382 T_ParsesFuncSumTailG_388
-- Once.Parser.Generic.Relation.Gen.atomShrink
d_atomShrink_676 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAtomG_366 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_atomShrink_676 v0 v1 v2 v3 v4
  = case coe v4 of
      C_pa'45'unit_392
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v3)))
      C_pa'45'void_396
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v3)))
      C_pa'45'int_400
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v3)))
      C_pa'45'float_404
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v3)))
      C_pa'45'eff_416 v6 v8 v9 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                    (coe
                       d_atomShrink_676 (coe v0) (coe v6) (coe v9) (coe v3) (coe v11))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v13)
                       (coe
                          d_atomShrink_676 (coe v0) (coe v13) (coe v8) (coe v6) (coe v10))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v14 = \ v14 -> addInt (coe (1 :: Integer)) (coe v14) in
                                 coe (coe (\ v15 -> v14)))
                                (coe (0 :: Integer)) (coe v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'act_428 v6 v8 v9 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                    (coe
                       d_atomShrink_676 (coe v0) (coe v6) (coe v9) (coe v3) (coe v11))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v13)
                       (coe
                          d_atomShrink_676 (coe v0) (coe v13) (coe v8) (coe v6) (coe v10))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v14 = \ v14 -> addInt (coe (1 :: Integer)) (coe v14) in
                                 coe (coe (\ v15 -> v14)))
                                (coe (0 :: Integer)) (coe v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'mu_436 v7 v8
        -> case coe v1 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                    (coe du_funcSumShrink_764 (coe v0) (coe v10) (coe v8))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v11 = \ v11 -> addInt (coe (1 :: Integer)) (coe v11) in
                              coe (coe (\ v12 -> v11)))
                             (coe (0 :: Integer)) (coe v10))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'nu_444 v7 v8
        -> case coe v1 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                    (coe du_funcSumShrink_764 (coe v0) (coe v10) (coe v8))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v11 = \ v11 -> addInt (coe (1 :: Integer)) (coe v11) in
                              coe (coe (\ v12 -> v11)))
                             (coe (0 :: Integer)) (coe v10))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pa'45'nu'45'eff_452 v7 v8
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
                                           (coe du_funcSumShrink_764 (coe v0) (coe v14) (coe v8)))
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
      C_pa'45'nu'45'act_460 v7 v8
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
                                           (coe du_funcSumShrink_764 (coe v0) (coe v14) (coe v8)))
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
      C_pa'45'extra_468 v8 -> coe d_extraShrink_196 v0 v1 v2 v3 v8
      C_pa'45'paren_478 v6 v9
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
                          du_typeShrink_730 (coe v0) (coe v12)
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
d_prodShrink_684 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdG_368 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodShrink_684 v0 v1 ~v2 ~v3 v4 = du_prodShrink_684 v0 v1 v4
du_prodShrink_684 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdG_368 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_prodShrink_684 v0 v1 v2
  = case coe v2 of
      C_pp'45'mk_490 v4 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_prodTailShrink_694 (coe v0) (coe v4) (coe v9))
             (coe d_atomShrink_676 (coe v0) (coe v1) (coe v6) (coe v4) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.prodTailShrink
d_prodTailShrink_694 ::
  T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdTailG_370 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodTailShrink_694 v0 ~v1 v2 ~v3 ~v4 v5
  = du_prodTailShrink_694 v0 v2 v5
du_prodTailShrink_694 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesProdTailG_370 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_prodTailShrink_694 v0 v1 v2
  = case coe v2 of
      C_ppt'45'done_496
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      C_ppt'45'star_510 v5 v7 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                (coe du_prodTailShrink_694 (coe v0) (coe v5) (coe v11))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                   (coe
                      d_atomShrink_676 (coe v0) (coe d_drop1_24 (coe v1)) (coe v7)
                      (coe v5) (coe v10))
                   (coe d_drop1'45''8804'_30 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.sumShrink
d_sumShrink_702 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumG_372 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumShrink_702 v0 v1 ~v2 ~v3 v4 = du_sumShrink_702 v0 v1 v4
du_sumShrink_702 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumG_372 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sumShrink_702 v0 v1 v2
  = case coe v2 of
      C_ps'45'mk_522 v4 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_sumTailShrink_712 (coe v0) (coe v4) (coe v9))
             (coe du_prodShrink_684 (coe v0) (coe v1) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.sumTailShrink
d_sumTailShrink_712 ::
  T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumTailG_374 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumTailShrink_712 v0 ~v1 v2 ~v3 ~v4 v5
  = du_sumTailShrink_712 v0 v2 v5
du_sumTailShrink_712 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesSumTailG_374 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sumTailShrink_712 v0 v1 v2
  = case coe v2 of
      C_pst'45'done_528
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      C_pst'45'plus_542 v5 v7 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                (coe du_sumTailShrink_712 (coe v0) (coe v5) (coe v11))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                   (coe
                      du_prodShrink_684 (coe v0) (coe d_drop1_24 (coe v1)) (coe v10))
                   (coe d_drop1'45''8804'_30 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.arrowTailShrink
d_arrowTailShrink_722 ::
  T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesArrowTailG_378 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowTailShrink_722 v0 ~v1 v2 ~v3 v4 v5
  = du_arrowTailShrink_722 v0 v2 v4 v5
du_arrowTailShrink_722 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesArrowTailG_378 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_arrowTailShrink_722 v0 v1 v2 v3
  = case coe v3 of
      C_pat'45'done_560
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      C_pat'45'arrow'45'g_572 v7 v8 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe
                   du_typeShrink_730 (coe v0) (coe d_drop2_34 (coe v1)) (coe v2)
                   (coe v10))
                (coe d_drop2'45''8804'_42 (coe v1)))
      C_pat'45'arrow_582 v7 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe
                   du_typeShrink_730 (coe v0) (coe d_drop1_24 (coe v1)) (coe v2)
                   (coe v9))
                (coe d_drop1'45''8804'_30 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.typeShrink
d_typeShrink_730 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesTypeG_376 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_typeShrink_730 v0 v1 ~v2 v3 v4 = du_typeShrink_730 v0 v1 v3 v4
du_typeShrink_730 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesTypeG_376 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_typeShrink_730 v0 v1 v2 v3
  = case coe v3 of
      C_pt'45'mk_554 v5 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_arrowTailShrink_722 (coe v0) (coe v5) (coe v2) (coe v10))
             (coe du_sumShrink_702 (coe v0) (coe v1) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.funcAtomShrink
d_funcAtomShrink_738 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncAtomG_380 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcAtomShrink_738 v0 v1 v2 v3 v4
  = case coe v4 of
      C_pfa'45'id_586
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v3)))
      C_pfa'45'k_594 v7 v8
        -> case coe v1 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                    (coe
                       d_atomShrink_676 (coe v0) (coe v10) (coe v7) (coe v3) (coe v8))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v11 = \ v11 -> addInt (coe (1 :: Integer)) (coe v11) in
                              coe (coe (\ v12 -> v11)))
                             (coe (0 :: Integer)) (coe v10))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pfa'45'paren_604 v6 v9
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
                       (coe du_funcSumShrink_764 (coe v0) (coe v12) (coe v9))
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
d_funcProdShrink_746 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncProdG_382 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdShrink_746 v0 v1 ~v2 ~v3 v4
  = du_funcProdShrink_746 v0 v1 v4
du_funcProdShrink_746 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncProdG_382 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_funcProdShrink_746 v0 v1 v2
  = case coe v2 of
      C_pfp'45'mk_616 v4 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_funcProdTailShrink_756 (coe v0) (coe v4) (coe v9))
             (coe
                d_funcAtomShrink_738 (coe v0) (coe v1) (coe v6) (coe v4) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.funcProdTailShrink
d_funcProdTailShrink_756 ::
  T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncProdTailG_384 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdTailShrink_756 v0 ~v1 v2 ~v3 ~v4 v5
  = du_funcProdTailShrink_756 v0 v2 v5
du_funcProdTailShrink_756 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncProdTailG_384 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_funcProdTailShrink_756 v0 v1 v2
  = case coe v2 of
      C_pfpt'45'done_622
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      C_pfpt'45'star_636 v5 v7 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                (coe du_funcProdTailShrink_756 (coe v0) (coe v5) (coe v11))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                   (coe
                      d_funcAtomShrink_738 (coe v0) (coe d_drop1_24 (coe v1)) (coe v7)
                      (coe v5) (coe v10))
                   (coe d_drop1'45''8804'_30 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.funcSumShrink
d_funcSumShrink_764 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncSumG_386 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumShrink_764 v0 v1 ~v2 ~v3 v4
  = du_funcSumShrink_764 v0 v1 v4
du_funcSumShrink_764 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncSumG_386 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_funcSumShrink_764 v0 v1 v2
  = case coe v2 of
      C_pfs'45'mk_648 v4 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_funcSumTailShrink_774 (coe v0) (coe v4) (coe v9))
             (coe du_funcProdShrink_746 (coe v0) (coe v1) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Relation.Gen.funcSumTailShrink
d_funcSumTailShrink_774 ::
  T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncSumTailG_388 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumTailShrink_774 v0 ~v1 v2 ~v3 ~v4 v5
  = du_funcSumTailShrink_774 v0 v2 v5
du_funcSumTailShrink_774 ::
  T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesFuncSumTailG_388 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_funcSumTailShrink_774 v0 v1 v2
  = case coe v2 of
      C_pfst'45'done_654
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      C_pfst'45'plus_668 v5 v7 v10 v11
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                (coe du_funcSumTailShrink_774 (coe v0) (coe v5) (coe v11))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                   (coe
                      du_funcProdShrink_746 (coe v0) (coe d_drop1_24 (coe v1)) (coe v10))
                   (coe d_drop1'45''8804'_30 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
