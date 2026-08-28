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

module MAlonzo.Code.Once.Parser.Type where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Type.isUpperWord
d_isUpperWord_6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isUpperWord_6 v0
  = let v1
          = coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0 in
    coe
      (case coe v1 of
         [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         (:) v2 v3
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v2)
                (coe
                   MAlonzo.Code.Data.Bool.Base.d_not_22
                   (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsLower_8 v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.tryParseTypeVar
d_tryParseTypeVar_20 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tryParseTypeVar_20 ~v0 ~v1 = du_tryParseTypeVar_20
du_tryParseTypeVar_20 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tryParseTypeVar_20
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Parser.Type.ParseAtomD
d_ParseAtomD_22 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseAtomD_22 = erased
-- Once.Parser.Type.ParseProdD
d_ParseProdD_30 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseProdD_30 = erased
-- Once.Parser.Type.ParseSumD
d_ParseSumD_38 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseSumD_38 = erased
-- Once.Parser.Type.ParseTypeD
d_ParseTypeD_46 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseTypeD_46 = erased
-- Once.Parser.Type.ParseProdTailD
d_ParseProdTailD_54 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseProdTailD_54 = erased
-- Once.Parser.Type.ParseSumTailD
d_ParseSumTailD_64 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseSumTailD_64 = erased
-- Once.Parser.Type.ParseArrowTailD
d_ParseArrowTailD_74 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseArrowTailD_74 = erased
-- Once.Parser.Type.ParseFunctorAtomD
d_ParseFunctorAtomD_84 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseFunctorAtomD_84 = erased
-- Once.Parser.Type.ParseFunctorProdD
d_ParseFunctorProdD_92 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseFunctorProdD_92 = erased
-- Once.Parser.Type.ParseFunctorProdTailD
d_ParseFunctorProdTailD_100 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseFunctorProdTailD_100 = erased
-- Once.Parser.Type.ParseFunctorSumD
d_ParseFunctorSumD_110 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseFunctorSumD_110 = erased
-- Once.Parser.Type.ParseFunctorSumTailD
d_ParseFunctorSumTailD_118 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseFunctorSumTailD_118 = erased
-- Once.Parser.Type.parseTypeAtomWF
d_parseTypeAtomWF_130 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeAtomWF_130 v0 ~v1 = du_parseTypeAtomWF_130 v0
du_parseTypeAtomWF_130 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseTypeAtomWF_130 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Parser.Token.C_TWord_8 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v4 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v3))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v3)
                               (coe ("Unit" :: Data.Text.Text))) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                              (coe
                                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'unit_122))))
                              else coe
                                     seq (coe v6)
                                     (let v7
                                            = coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v7 ->
                                                   coe
                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                     (coe v3))
                                                (coe
                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                   (coe v3) (coe ("Void" :: Data.Text.Text))) in
                                      coe
                                        (case coe v7 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                             -> if coe v8
                                                  then coe
                                                         seq (coe v9)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Void_120)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe v2)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'void_126))))
                                                  else coe
                                                         seq (coe v9)
                                                         (let v10
                                                                = coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                    erased
                                                                    (\ v10 ->
                                                                       coe
                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                         (coe v3))
                                                                    (coe
                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                       (coe v3)
                                                                       (coe
                                                                          ("Int"
                                                                           ::
                                                                           Data.Text.Text))) in
                                                          coe
                                                            (case coe v10 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                                 -> if coe v11
                                                                      then coe
                                                                             seq (coe v12)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Type.C_Int_132)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      (coe v2)
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'int_130))))
                                                                      else coe
                                                                             seq (coe v12)
                                                                             (let v13
                                                                                    = coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                        erased
                                                                                        (\ v13 ->
                                                                                           coe
                                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                             (coe
                                                                                                v3))
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                           (coe v3)
                                                                                           (coe
                                                                                              ("Float"
                                                                                               ::
                                                                                               Data.Text.Text))) in
                                                                              coe
                                                                                (case coe v13 of
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                                     -> if coe v14
                                                                                          then coe
                                                                                                 seq
                                                                                                 (coe
                                                                                                    v15)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Type.C_Float_134)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                          (coe
                                                                                                             v2)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'float_134))))
                                                                                          else coe
                                                                                                 seq
                                                                                                 (coe
                                                                                                    v15)
                                                                                                 (let v16
                                                                                                        = coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                            erased
                                                                                                            (\ v16 ->
                                                                                                               coe
                                                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                 (coe
                                                                                                                    v3))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                               (coe
                                                                                                                  v3)
                                                                                                               (coe
                                                                                                                  ("Buffer"
                                                                                                                   ::
                                                                                                                   Data.Text.Text))) in
                                                                                                  coe
                                                                                                    (case coe
                                                                                                            v16 of
                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                                                         -> if coe
                                                                                                                 v17
                                                                                                              then coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Type.C_Buffer_138)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                              (coe
                                                                                                                                 v2)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'buffer_138))))
                                                                                                              else coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v18)
                                                                                                                     (let v19
                                                                                                                            = coe
                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                erased
                                                                                                                                (\ v19 ->
                                                                                                                                   coe
                                                                                                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                     (coe
                                                                                                                                        v3))
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                   (coe
                                                                                                                                      v3)
                                                                                                                                   (coe
                                                                                                                                      ("String"
                                                                                                                                       ::
                                                                                                                                       Data.Text.Text))) in
                                                                                                                      coe
                                                                                                                        (case coe
                                                                                                                                v19 of
                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                                             -> if coe
                                                                                                                                     v20
                                                                                                                                  then coe
                                                                                                                                         seq
                                                                                                                                         (coe
                                                                                                                                            v21)
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Once.Type.C_Str_136)
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                  (coe
                                                                                                                                                     v2)
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'string_142))))
                                                                                                                                  else coe
                                                                                                                                         seq
                                                                                                                                         (coe
                                                                                                                                            v21)
                                                                                                                                         (let v22
                                                                                                                                                = coe
                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                    erased
                                                                                                                                                    (\ v22 ->
                                                                                                                                                       coe
                                                                                                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                         (coe
                                                                                                                                                            v3))
                                                                                                                                                    (coe
                                                                                                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                       (coe
                                                                                                                                                          v3)
                                                                                                                                                       (coe
                                                                                                                                                          ("Eff"
                                                                                                                                                           ::
                                                                                                                                                           Data.Text.Text))) in
                                                                                                                                          coe
                                                                                                                                            (case coe
                                                                                                                                                    v22 of
                                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                                                                                 -> if coe
                                                                                                                                                         v23
                                                                                                                                                      then coe
                                                                                                                                                             seq
                                                                                                                                                             (coe
                                                                                                                                                                v24)
                                                                                                                                                             (let v25
                                                                                                                                                                    = coe
                                                                                                                                                                        du_parseTypeAtomWF_130
                                                                                                                                                                        (coe
                                                                                                                                                                           v2) in
                                                                                                                                                              coe
                                                                                                                                                                (case coe
                                                                                                                                                                        v25 of
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                                                                                     -> case coe
                                                                                                                                                                               v26 of
                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                                                                            -> case coe
                                                                                                                                                                                      v28 of
                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                                                                                                   -> let v31
                                                                                                                                                                                            = coe
                                                                                                                                                                                                du_parseTypeAtomWF_130
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   v29) in
                                                                                                                                                                                      coe
                                                                                                                                                                                        (case coe
                                                                                                                                                                                                v31 of
                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v32
                                                                                                                                                                                             -> case coe
                                                                                                                                                                                                       v32 of
                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                                                                                    -> case coe
                                                                                                                                                                                                              v34 of
                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                                                                                                                           -> coe
                                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         v27)
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            MAlonzo.Code.Once.Type.C_eff_36))
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         v33))
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         v35)
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'eff_154
                                                                                                                                                                                                                         v29
                                                                                                                                                                                                                         v30
                                                                                                                                                                                                                         v36)))
                                                                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                             -> coe
                                                                                                                                                                                                  v31
                                                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                     -> coe
                                                                                                                                                                          v25
                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                      else coe
                                                                                                                                                             seq
                                                                                                                                                             (coe
                                                                                                                                                                v24)
                                                                                                                                                             (let v25
                                                                                                                                                                    = coe
                                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                        erased
                                                                                                                                                                        (\ v25 ->
                                                                                                                                                                           coe
                                                                                                                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                             (coe
                                                                                                                                                                                v3))
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                           (coe
                                                                                                                                                                              v3)
                                                                                                                                                                           (coe
                                                                                                                                                                              ("IO"
                                                                                                                                                                               ::
                                                                                                                                                                               Data.Text.Text))) in
                                                                                                                                                              coe
                                                                                                                                                                (case coe
                                                                                                                                                                        v25 of
                                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                                                                                     -> if coe
                                                                                                                                                                             v26
                                                                                                                                                                          then coe
                                                                                                                                                                                 seq
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v27)
                                                                                                                                                                                 (let v28
                                                                                                                                                                                        = coe
                                                                                                                                                                                            du_parseTypeAtomWF_130
                                                                                                                                                                                            (coe
                                                                                                                                                                                               v2) in
                                                                                                                                                                                  coe
                                                                                                                                                                                    (case coe
                                                                                                                                                                                            v28 of
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                                                                                                                                                                                         -> case coe
                                                                                                                                                                                                   v29 of
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                                                                                -> case coe
                                                                                                                                                                                                          v31 of
                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                                                                                                       -> coe
                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Once.Type.C_Unit_118)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        MAlonzo.Code.Once.Type.C_eff_36))
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v30))
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v32)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'io_162
                                                                                                                                                                                                                     v33)))
                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                         -> coe
                                                                                                                                                                                              v28
                                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                          else coe
                                                                                                                                                                                 seq
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v27)
                                                                                                                                                                                 (let v28
                                                                                                                                                                                        = coe
                                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                            erased
                                                                                                                                                                                            (\ v28 ->
                                                                                                                                                                                               coe
                                                                                                                                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    v3))
                                                                                                                                                                                            (coe
                                                                                                                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  v3)
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  ("Mu"
                                                                                                                                                                                                   ::
                                                                                                                                                                                                   Data.Text.Text))) in
                                                                                                                                                                                  coe
                                                                                                                                                                                    (case coe
                                                                                                                                                                                            v28 of
                                                                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v29 v30
                                                                                                                                                                                         -> if coe
                                                                                                                                                                                                 v29
                                                                                                                                                                                              then coe
                                                                                                                                                                                                     seq
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v30)
                                                                                                                                                                                                     (let v31
                                                                                                                                                                                                            = coe
                                                                                                                                                                                                                du_parseFunctorSumWF_178
                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                   v2) in
                                                                                                                                                                                                      coe
                                                                                                                                                                                                        (case coe
                                                                                                                                                                                                                v31 of
                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v32
                                                                                                                                                                                                             -> case coe
                                                                                                                                                                                                                       v32 of
                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                                                                                                    -> case coe
                                                                                                                                                                                                                              v34 of
                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                                                                                                                                           -> coe
                                                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                      MAlonzo.Code.Once.Type.C_μ'45'type_128
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v33))
                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v35)
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'mu_180
                                                                                                                                                                                                                                         v36)))
                                                                                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                             -> coe
                                                                                                                                                                                                                  v31
                                                                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                              else coe
                                                                                                                                                                                                     seq
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v30)
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Token.C_TInt_10 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v3 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TString_14 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> coe du_parseTypeAtomWF'45'TLParen_192 (coe v2)
             MAlonzo.Code.Once.Parser.Token.C_TRParen_18
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TColon_24
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TEquals_26
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TArrow_28
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TLambda_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TComma_38
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TAt_42
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TPipe_44
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TDot_46
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TPlus_48
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TMinus_50
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TStar_52
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TSlash_54
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TPercent_56
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TLt_60
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TLe_62
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TGt_64
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TGe_66
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TNeq_70
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TBang_72
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TNewline_74
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TEOF_76
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.parseTypeWF
d_parseTypeWF_134 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeWF_134 v0 ~v1 = du_parseTypeWF_134 v0
du_parseTypeWF_134 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseTypeWF_134 v0
  = let v1 = coe du_parseTypeAtomWF_130 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7 = coe du_parseTypeProdTailWF_148 (coe v3) (coe v5) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                 -> let v13
                                                          = coe
                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192
                                                              v5 v3 v6 v12 in
                                                    coe
                                                      (let v14
                                                             = coe
                                                                 du_parseTypeSumTailWF_154 (coe v9)
                                                                 (coe v11) in
                                                       coe
                                                         (case coe v14 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                              -> case coe v15 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                     -> case coe v17 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                            -> let v20
                                                                                     = coe
                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                                         v11 v9 v13
                                                                                         v19 in
                                                                               coe
                                                                                 (let v21
                                                                                        = coe
                                                                                            du_parseArrowTailWF_160
                                                                                            (coe
                                                                                               v16)
                                                                                            (coe
                                                                                               v18) in
                                                                                  coe
                                                                                    (case coe v21 of
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                                                                         -> case coe
                                                                                                   v22 of
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                -> case coe
                                                                                                          v24 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                       -> coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               (coe
                                                                                                                  v23)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                  (coe
                                                                                                                     v25)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                     v18
                                                                                                                     v16
                                                                                                                     v20
                                                                                                                     v26)))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                         -> coe v21
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                     -> case coe v15 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                            -> case coe v17 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                   -> let v20
                                                                                            = coe
                                                                                                du_parseArrowTailWF_160
                                                                                                (coe
                                                                                                   v16)
                                                                                                (coe
                                                                                                   v18) in
                                                                                      coe
                                                                                        (case coe
                                                                                                v20 of
                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                             -> case coe
                                                                                                       v21 of
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                    -> case coe
                                                                                                              v23 of
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                                           -> coe
                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      v22)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                      (coe
                                                                                                                         v24)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                         v18
                                                                                                                         v16
                                                                                                                         v19
                                                                                                                         v25)))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                             -> coe
                                                                                                  v20
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe v14
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> let v13
                                                                 = coe
                                                                     du_parseTypeSumTailWF_154
                                                                     (coe v9) (coe v11) in
                                                           coe
                                                             (case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                         -> case coe v16 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                -> let v19
                                                                                         = coe
                                                                                             MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                                             v11 v9
                                                                                             v12
                                                                                             v18 in
                                                                                   coe
                                                                                     (let v20
                                                                                            = coe
                                                                                                du_parseArrowTailWF_160
                                                                                                (coe
                                                                                                   v15)
                                                                                                (coe
                                                                                                   v17) in
                                                                                      coe
                                                                                        (case coe
                                                                                                v20 of
                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                             -> case coe
                                                                                                       v21 of
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                    -> case coe
                                                                                                              v23 of
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                                           -> coe
                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      v22)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                      (coe
                                                                                                                         v24)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                         v17
                                                                                                                         v15
                                                                                                                         v19
                                                                                                                         v25)))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                             -> coe
                                                                                                  v20
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> case coe v13 of
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                         -> case coe v14 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                -> case coe v16 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                       -> let v19
                                                                                                = coe
                                                                                                    du_parseArrowTailWF_160
                                                                                                    (coe
                                                                                                       v15)
                                                                                                    (coe
                                                                                                       v17) in
                                                                                          coe
                                                                                            (case coe
                                                                                                    v19 of
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                                 -> case coe
                                                                                                           v20 of
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                        -> case coe
                                                                                                                  v22 of
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                               -> coe
                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                       (coe
                                                                                                                          v21)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                          (coe
                                                                                                                             v23)
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                             v17
                                                                                                                             v15
                                                                                                                             v18
                                                                                                                             v24)))
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                 -> coe
                                                                                                      v19
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                         -> coe v13
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                 -> case coe v8 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                        -> case coe v10 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                               -> let v13
                                                                        = coe
                                                                            du_parseArrowTailWF_160
                                                                            (coe v9) (coe v11) in
                                                                  coe
                                                                    (case coe v13 of
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                         -> case coe v14 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                -> case coe v16 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                       -> coe
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  v15)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     v17)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                     v11
                                                                                                     v9
                                                                                                     v12
                                                                                                     v18)))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                         -> coe v13
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v7
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                         -> case coe v4 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                -> let v7 = coe du_parseTypeSumTailWF_154 (coe v3) (coe v5) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> let v13
                                                                 = coe
                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                     v5 v3 v6 v12 in
                                                           coe
                                                             (let v14
                                                                    = coe
                                                                        du_parseArrowTailWF_160
                                                                        (coe v9) (coe v11) in
                                                              coe
                                                                (case coe v14 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                     -> case coe v15 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                            -> case coe v17 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                   -> coe
                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v16)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 v18)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                 v11
                                                                                                 v9
                                                                                                 v13
                                                                                                 v19)))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe v14
                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                 -> case coe v8 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                        -> case coe v10 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                               -> let v13
                                                                        = coe
                                                                            du_parseArrowTailWF_160
                                                                            (coe v9) (coe v11) in
                                                                  coe
                                                                    (case coe v13 of
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                         -> case coe v14 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                -> case coe v16 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                       -> coe
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  v15)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     v17)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                     v11
                                                                                                     v9
                                                                                                     v12
                                                                                                     v18)))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                         -> coe v13
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v7
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                                -> case coe v4 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                       -> let v7 = coe du_parseArrowTailWF_160 (coe v3) (coe v5) in
                                          coe
                                            (case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                 -> case coe v8 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                        -> case coe v10 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v9)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v11)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                             v5 v3 v6 v12)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v7
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.parseTypeSumWF
d_parseTypeSumWF_138 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeSumWF_138 v0 ~v1 = du_parseTypeSumWF_138 v0
du_parseTypeSumWF_138 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseTypeSumWF_138 v0
  = let v1 = coe du_parseTypeAtomWF_130 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7 = coe du_parseTypeProdTailWF_148 (coe v3) (coe v5) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                 -> let v13
                                                          = coe
                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192
                                                              v5 v3 v6 v12 in
                                                    coe
                                                      (let v14
                                                             = coe
                                                                 du_parseTypeSumTailWF_154 (coe v9)
                                                                 (coe v11) in
                                                       coe
                                                         (case coe v14 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                              -> case coe v15 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                     -> case coe v17 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe v16)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v18)
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                                          v11 v9 v13
                                                                                          v19)))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe v14
                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> let v13
                                                                 = coe
                                                                     du_parseTypeSumTailWF_154
                                                                     (coe v9) (coe v11) in
                                                           coe
                                                             (case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                         -> case coe v16 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                -> coe
                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe v15)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v17)
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                                              v11 v9
                                                                                              v12
                                                                                              v18)))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> coe v13
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                         -> case coe v4 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                -> let v7 = coe du_parseTypeSumTailWF_154 (coe v3) (coe v5) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v9)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v11)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                      v5 v3 v6 v12)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.parseTypeProdWF
d_parseTypeProdWF_142 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeProdWF_142 v0 ~v1 = du_parseTypeProdWF_142 v0
du_parseTypeProdWF_142 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseTypeProdWF_142 v0
  = let v1 = coe du_parseTypeAtomWF_130 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7 = coe du_parseTypeProdTailWF_148 (coe v3) (coe v5) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v9)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192
                                                               v5 v3 v6 v12)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.parseTypeProdTailWF
d_parseTypeProdTailWF_148 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeProdTailWF_148 v0 v1 ~v2
  = du_parseTypeProdTailWF_148 v0 v1
du_parseTypeProdTailWF_148 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseTypeProdTailWF_148 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TInt_10 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v4 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TString_14 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TRParen_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TColon_24
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEquals_26
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TArrow_28
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLambda_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TComma_38
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TAt_42
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPipe_44
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TDot_46
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPlus_48
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TMinus_50
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TStar_52
               -> let v4 = coe du_parseTypeAtomWF_130 (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> let v10
                                                = coe
                                                    du_parseTypeProdTailWF_148
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'42'__122 (coe v0)
                                                       (coe v6))
                                                    (coe v8) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> case coe v13 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v14)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'star_212
                                                                             v8 v6 v9 v15)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v10
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Token.C_TSlash_54
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPercent_56
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLt_60
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLe_62
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TGt_64
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TGe_66
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TNeq_70
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TBang_72
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TNewline_74
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEOF_76
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.parseTypeSumTailWF
d_parseTypeSumTailWF_154 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeSumTailWF_154 v0 v1 ~v2
  = du_parseTypeSumTailWF_154 v0 v1
du_parseTypeSumTailWF_154 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseTypeSumTailWF_154 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TInt_10 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v4 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TString_14 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TRParen_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TColon_24
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEquals_26
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TArrow_28
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLambda_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TComma_38
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TAt_42
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPipe_44
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TDot_46
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPlus_48
               -> let v4 = coe du_parseTypeProdWF_142 (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> let v10
                                                = coe
                                                    du_parseTypeSumTailWF_154
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'43'__124 (coe v0)
                                                       (coe v6))
                                                    (coe v8) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> case coe v13 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v14)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'plus_244
                                                                             v8 v6 v9 v15)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v10
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Token.C_TMinus_50
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TStar_52
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TSlash_54
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPercent_56
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLt_60
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLe_62
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TGt_64
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TGe_66
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TNeq_70
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TBang_72
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TNewline_74
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEOF_76
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.parseArrowTailWF
d_parseArrowTailWF_160 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseArrowTailWF_160 v0 v1 ~v2 = du_parseArrowTailWF_160 v0 v1
du_parseArrowTailWF_160 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseArrowTailWF_160 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TInt_10 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v4 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TString_14 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TRParen_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TColon_24
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEquals_26
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TArrow_28
               -> let v4 = coe du_parseTypeWF_134 (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                  (coe v0)
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                  (coe v6))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow_284
                                                     v9)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
               -> let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
                  coe
                    (case coe v3 of
                       (:) v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                -> let v7 = coe du_parseTypeWF_134 (coe v6) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                   (coe v0)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_One_8)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_pure_34))
                                                                   (coe v9))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v11)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_274
                                                                      v12)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v4
                       _ -> coe v4)
             MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
               -> let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
                  coe
                    (case coe v3 of
                       (:) v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                -> let v7 = coe du_parseTypeWF_134 (coe v6) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                   (coe v0)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Zero_6)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_pure_34))
                                                                   (coe v9))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v11)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_274
                                                                      v12)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v4
                       _ -> coe v4)
             MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
               -> let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
                  coe
                    (case coe v3 of
                       (:) v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                -> let v7 = coe du_parseTypeWF_134 (coe v6) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                   (coe v0)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_pure_34))
                                                                   (coe v9))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v11)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_274
                                                                      v12)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v4
                       _ -> coe v4)
             MAlonzo.Code.Once.Parser.Token.C_TLambda_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TComma_38
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TAt_42
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPipe_44
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TDot_46
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPlus_48
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TMinus_50
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TStar_52
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TSlash_54
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPercent_56
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLt_60
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLe_62
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TGt_64
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TGe_66
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TNeq_70
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TBang_72
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TNewline_74
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEOF_76
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.parseFunctorAtomWF
d_parseFunctorAtomWF_164 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseFunctorAtomWF_164 v0 ~v1 = du_parseFunctorAtomWF_164 v0
du_parseFunctorAtomWF_164 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseFunctorAtomWF_164 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
                  -> let v5
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v5 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe ("Id" :: Data.Text.Text))) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                            -> if coe v6
                                 then coe
                                        seq (coe v7)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe MAlonzo.Code.Once.Type.C_Id_112)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v3)
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'id_288))))
                                 else coe
                                        seq (coe v7)
                                        (let v8
                                               = coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                   erased
                                                   (\ v8 ->
                                                      coe
                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                        (coe v4))
                                                   (coe
                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                      (coe v4) (coe ("K" :: Data.Text.Text))) in
                                         coe
                                           (case coe v8 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                -> if coe v9
                                                     then coe
                                                            seq (coe v10)
                                                            (let v11
                                                                   = coe
                                                                       du_parseTypeAtomWF_130
                                                                       (coe v3) in
                                                             coe
                                                               (case coe v11 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                    -> case coe v12 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                           -> case coe v14 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                  -> coe
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Type.C_K_110
                                                                                             (coe
                                                                                                v13))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                v15)
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'k_296
                                                                                                v16)))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> coe v11
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                     else coe
                                                            seq (coe v10)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                  -> coe du_parseFunctorAtomWF'45'TLParen_188 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Type.parseFunctorProdWF
d_parseFunctorProdWF_168 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseFunctorProdWF_168 v0 ~v1 = du_parseFunctorProdWF_168 v0
du_parseFunctorProdWF_168 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseFunctorProdWF_168 v0
  = let v1 = coe du_parseFunctorAtomWF_164 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7 = coe du_parseFunctorProdTailWF_174 (coe v3) (coe v5) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v9)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.TypeRelation.C_pfp'45'mk_318
                                                               v5 v3 v6 v12)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.parseFunctorProdTailWF
d_parseFunctorProdTailWF_174 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseFunctorProdTailWF_174 v0 v1 ~v2
  = du_parseFunctorProdTailWF_174 v0 v1
du_parseFunctorProdTailWF_174 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseFunctorProdTailWF_174 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TInt_10 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v4 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TString_14 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TRParen_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TColon_24
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEquals_26
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TArrow_28
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLambda_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TComma_38
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TAt_42
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPipe_44
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TDot_46
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPlus_48
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TMinus_50
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TStar_52
               -> let v4 = coe du_parseFunctorAtomWF_164 (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> let v10
                                                = coe
                                                    du_parseFunctorProdTailWF_174
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8855'__116
                                                       (coe v0) (coe v6))
                                                    (coe v8) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> case coe v13 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v14)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'star_338
                                                                             v8 v6 v9 v15)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v10
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Token.C_TSlash_54
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPercent_56
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLt_60
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLe_62
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TGt_64
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TGe_66
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TNeq_70
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TBang_72
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TNewline_74
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEOF_76
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.parseFunctorSumWF
d_parseFunctorSumWF_178 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseFunctorSumWF_178 v0 ~v1 = du_parseFunctorSumWF_178 v0
du_parseFunctorSumWF_178 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseFunctorSumWF_178 v0
  = let v1 = coe du_parseFunctorAtomWF_164 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7 = coe du_parseFunctorProdTailWF_174 (coe v3) (coe v5) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                 -> let v13
                                                          = coe
                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_pfp'45'mk_318
                                                              v5 v3 v6 v12 in
                                                    coe
                                                      (let v14
                                                             = coe
                                                                 du_parseFunctorSumTailWF_184
                                                                 (coe v9) (coe v11) in
                                                       coe
                                                         (case coe v14 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                              -> case coe v15 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                     -> case coe v17 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe v16)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v18)
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.TypeRelation.C_pfs'45'mk_350
                                                                                          v11 v9 v13
                                                                                          v19)))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe v14
                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> let v13
                                                                 = coe
                                                                     du_parseFunctorSumTailWF_184
                                                                     (coe v9) (coe v11) in
                                                           coe
                                                             (case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                         -> case coe v16 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                -> coe
                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe v15)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v17)
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_pfs'45'mk_350
                                                                                              v11 v9
                                                                                              v12
                                                                                              v18)))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> coe v13
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                         -> case coe v4 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                -> let v7 = coe du_parseFunctorSumTailWF_184 (coe v3) (coe v5) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v9)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v11)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_pfs'45'mk_350
                                                                      v5 v3 v6 v12)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.parseFunctorSumTailWF
d_parseFunctorSumTailWF_184 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseFunctorSumTailWF_184 v0 v1 ~v2
  = du_parseFunctorSumTailWF_184 v0 v1
du_parseFunctorSumTailWF_184 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseFunctorSumTailWF_184 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TInt_10 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v4 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TString_14 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TRParen_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TColon_24
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEquals_26
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TArrow_28
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLambda_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TComma_38
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TAt_42
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPipe_44
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TDot_46
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPlus_48
               -> let v4 = coe du_parseFunctorProdWF_168 (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> let v10
                                                = coe
                                                    du_parseFunctorSumTailWF_184
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8853'__114
                                                       (coe v0) (coe v6))
                                                    (coe v8) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> case coe v13 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v14)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'plus_370
                                                                             v8 v6 v9 v15)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v10
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Token.C_TMinus_50
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TStar_52
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TSlash_54
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TPercent_56
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLt_60
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TLe_62
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TGt_64
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TGe_66
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TNeq_70
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TBang_72
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TNewline_74
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             MAlonzo.Code.Once.Parser.Token.C_TEOF_76
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.parseFunctorAtomWF-TLParen
d_parseFunctorAtomWF'45'TLParen_188 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseFunctorAtomWF'45'TLParen_188 v0 ~v1
  = du_parseFunctorAtomWF'45'TLParen_188 v0
du_parseFunctorAtomWF'45'TLParen_188 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseFunctorAtomWF'45'TLParen_188 v0
  = let v1 = coe du_parseFunctorSumWF_178 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> case coe v5 of
                              (:) v7 v8
                                -> case coe v7 of
                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'paren_306
                                                     v5 v6)))
                                     _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                              _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.parseTypeAtomWF-TLParen
d_parseTypeAtomWF'45'TLParen_192 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeAtomWF'45'TLParen_192 v0 ~v1
  = du_parseTypeAtomWF'45'TLParen_192 v0
du_parseTypeAtomWF'45'TLParen_192 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseTypeAtomWF'45'TLParen_192 v0
  = let v1 = coe du_parseTypeWF_134 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> case coe v5 of
                              [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                              (:) v7 v8
                                -> case coe v7 of
                                     MAlonzo.Code.Once.Parser.Token.C_TWord_8 v9
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TInt_10 v9 v10
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v9 v10 v11 v12
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TString_14 v9
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_172
                                                     v5 v6)))
                                     MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TColon_24
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TEquals_26
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TLambda_36
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TComma_38
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TAt_42
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TPipe_44
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TDot_46
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TPlus_48
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TMinus_50
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TStar_52
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TSlash_54
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TPercent_56
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TLt_60
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TLe_62
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TGt_64
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TGe_66
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TNeq_70
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TBang_72
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TNewline_74
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     MAlonzo.Code.Once.Parser.Token.C_TEOF_76
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.stripAtom
d_stripAtom_2722 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripAtom_2722 ~v0 v1 = du_stripAtom_2722 v1
du_stripAtom_2722 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripAtom_2722 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.stripProd
d_stripProd_2730 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripProd_2730 ~v0 v1 = du_stripProd_2730 v1
du_stripProd_2730 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripProd_2730 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.stripSum
d_stripSum_2738 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripSum_2738 ~v0 v1 = du_stripSum_2738 v1
du_stripSum_2738 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripSum_2738 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.stripType
d_stripType_2746 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripType_2746 ~v0 v1 = du_stripType_2746 v1
du_stripType_2746 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripType_2746 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.stripProdTail
d_stripProdTail_2756 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripProdTail_2756 ~v0 ~v1 v2 = du_stripProdTail_2756 v2
du_stripProdTail_2756 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripProdTail_2756 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.stripSumTail
d_stripSumTail_2766 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripSumTail_2766 ~v0 ~v1 v2 = du_stripSumTail_2766 v2
du_stripSumTail_2766 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripSumTail_2766 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.stripArrowTail
d_stripArrowTail_2776 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripArrowTail_2776 ~v0 ~v1 v2 = du_stripArrowTail_2776 v2
du_stripArrowTail_2776 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripArrowTail_2776 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.parseType
d_parseType_2782 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseType_2782 v0
  = coe du_stripType_2746 (coe du_parseTypeWF_134 (coe v0))
-- Once.Parser.Type.parseTypeAtom
d_parseTypeAtom_2786 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeAtom_2786 v0
  = coe du_stripAtom_2722 (coe du_parseTypeAtomWF_130 (coe v0))
-- Once.Parser.Type.parseTypeSum
d_parseTypeSum_2790 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeSum_2790 v0
  = coe du_stripSum_2738 (coe du_parseTypeSumWF_138 (coe v0))
-- Once.Parser.Type.parseTypeProd
d_parseTypeProd_2794 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeProd_2794 v0
  = coe du_stripProd_2730 (coe du_parseTypeProdWF_142 (coe v0))
-- Once.Parser.Type.parseTypeProdTail
d_parseTypeProdTail_2800 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeProdTail_2800 v0 v1
  = coe
      du_stripProdTail_2756
      (coe du_parseTypeProdTailWF_148 (coe v0) (coe v1))
-- Once.Parser.Type.parseTypeSumTail
d_parseTypeSumTail_2808 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeSumTail_2808 v0 v1
  = coe
      du_stripSumTail_2766
      (coe du_parseTypeSumTailWF_154 (coe v0) (coe v1))
-- Once.Parser.Type.parseArrowTail
d_parseArrowTail_2816 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseArrowTail_2816 v0 v1
  = coe
      du_stripArrowTail_2776
      (coe du_parseArrowTailWF_160 (coe v0) (coe v1))
