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

module MAlonzo.Code.Once.Grammar.Convert where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Type

-- Once.Grammar.Convert.gtypeToType
d_gtypeToType_6 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_gtypeToType_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_TUnit_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Unit_118)
      MAlonzo.Code.Once.Grammar.C_TVoid_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Void_120)
      MAlonzo.Code.Once.Grammar.C_TInt_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Int_132)
      MAlonzo.Code.Once.Grammar.C_TFloat_16
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Float_134)
      MAlonzo.Code.Once.Grammar.C_TBuffer_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Buffer_138)
      MAlonzo.Code.Once.Grammar.C_TString_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Str_136)
      MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__22 v1 v2 v3
        -> let v4 = d_gtypeToType_6 (coe v1) in
           coe
             (let v5 = d_gtypeToType_6 (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v2)
                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                    (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C__'8855'__24 v1 v2
        -> let v3 = d_gtypeToType_6 (coe v1) in
           coe
             (let v4 = d_gtypeToType_6 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C__'8853'__26 v1 v2
        -> let v3 = d_gtypeToType_6 (coe v1) in
           coe
             (let v4 = d_gtypeToType_6 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_TEff_28 v1 v2
        -> let v3 = d_gtypeToType_6 (coe v1) in
           coe
             (let v4 = d_gtypeToType_6 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v5)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                    (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_TVar_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Convert.typeToGType
d_typeToGType_94 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Grammar.T_GType_8
d_typeToGType_94 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_TUnit_10)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_TVoid_12)
      MAlonzo.Code.Once.Type.C__'42'__122 v1 v2
        -> let v3 = d_typeToGType_94 (coe v1) in
           coe
             (let v4 = d_typeToGType_94 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Grammar.C__'8855'__24 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Type.C__'43'__124 v1 v2
        -> let v3 = d_typeToGType_94 (coe v1) in
           coe
             (let v4 = d_typeToGType_94 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Grammar.C__'8853'__26 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_pure_34
                      -> let v6 = d_typeToGType_94 (coe v1) in
                         coe
                           (let v7 = d_typeToGType_94 (coe v3) in
                            coe
                              (case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__22
                                                  (coe v8) (coe v4) (coe v9))
                                        _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                 _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                    MAlonzo.Code.Once.Type.C_eff_36
                      -> case coe v4 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           MAlonzo.Code.Once.Type.C_One_8
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> let v6 = d_typeToGType_94 (coe v1) in
                                coe
                                  (let v7 = d_typeToGType_94 (coe v3) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Once.Grammar.C_TEff_28
                                                         (coe v8) (coe v9))
                                               _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                        _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_TInt_14)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_TFloat_16)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_TString_20)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_TBuffer_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Convert.typeToGType-gtypeToType
d_typeToGType'45'gtypeToType_186 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_typeToGType'45'gtypeToType_186 = erased
-- Once.Grammar.Convert.gtypeToType-typeToGType
d_gtypeToType'45'typeToGType_324 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gtypeToType'45'typeToGType_324 = erased
-- Once.Grammar.Convert.GrammarExpressible
d_GrammarExpressible_458 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_GrammarExpressible_458 = erased
-- Once.Grammar.Convert.parseGType
d_parseGType_464 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseGType_464 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Parser.Type.du_stripType_1670
              (let v1
                     = coe
                         MAlonzo.Code.Once.Parser.Type.du_parseTypeAtomWF_86 (coe v0) in
               coe
                 (case coe v1 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                    -> let v7
                                             = coe
                                                 MAlonzo.Code.Once.Parser.Type.du_parseTypeProdTailWF_104
                                                 (coe v3) (coe v5) in
                                       coe
                                         (case coe v7 of
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                              -> case coe v8 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                     -> case coe v10 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                            -> let v13
                                                                     = coe
                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_174
                                                                         v5 v3 v6 v12 in
                                                               coe
                                                                 (let v14
                                                                        = coe
                                                                            MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                            (coe v9) (coe v11) in
                                                                  coe
                                                                    (case coe v14 of
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                         -> case coe v15 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                -> case coe v17 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                       -> let v20
                                                                                                = coe
                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                    v11
                                                                                                    v9
                                                                                                    v13
                                                                                                    v19 in
                                                                                          coe
                                                                                            (let v21
                                                                                                   = coe
                                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                       (coe
                                                                                                          v16)
                                                                                                       (coe
                                                                                                          v18) in
                                                                                             coe
                                                                                               (case coe
                                                                                                       v21 of
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
                                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                v18
                                                                                                                                v16
                                                                                                                                v20
                                                                                                                                v26)))
                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                    -> coe
                                                                                                         v21
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                         -> case coe v14 of
                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                                -> case coe v15 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                       -> case coe
                                                                                                 v17 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                              -> let v20
                                                                                                       = coe
                                                                                                           MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
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
                                                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
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
                                                                                MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                (coe v9)
                                                                                (coe v11) in
                                                                      coe
                                                                        (case coe v13 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                             -> case coe v14 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                    -> case coe
                                                                                              v16 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                           -> let v19
                                                                                                    = coe
                                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                        v11
                                                                                                        v9
                                                                                                        v12
                                                                                                        v18 in
                                                                                              coe
                                                                                                (let v20
                                                                                                       = coe
                                                                                                           MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
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
                                                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
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
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                           -> case coe
                                                                                                     v16 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                  -> let v19
                                                                                                           = coe
                                                                                                               MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
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
                                                                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
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
                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                       (coe v9)
                                                                                       (coe v11) in
                                                                             coe
                                                                               (case coe v13 of
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                           -> case coe
                                                                                                     v16 of
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
                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
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
                                           -> let v7
                                                    = coe
                                                        MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                        (coe v3) (coe v5) in
                                              coe
                                                (case coe v7 of
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                     -> case coe v8 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                            -> case coe v10 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                   -> let v13
                                                                            = coe
                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                v5 v3 v6 v12 in
                                                                      coe
                                                                        (let v14
                                                                               = coe
                                                                                   MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                   (coe v9)
                                                                                   (coe v11) in
                                                                         coe
                                                                           (case coe v14 of
                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                                -> case coe v15 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                       -> case coe
                                                                                                 v17 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                              -> coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                      (coe
                                                                                                         v16)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            v18)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
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
                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                       (coe v9)
                                                                                       (coe v11) in
                                                                             coe
                                                                               (case coe v13 of
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                           -> case coe
                                                                                                     v16 of
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
                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
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
                                                  -> let v7
                                                           = coe
                                                               MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                               (coe v3) (coe v5) in
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
                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                        v5 v3 v6
                                                                                        v12)))
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
                    _ -> MAlonzo.RTE.mazUnreachableError)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> let v5 = d_typeToGType_94 (coe v3) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v4))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Grammar.Convert.NoMuNu
d_NoMuNu_512 a0 = ()
data T_NoMuNu_512
  = C_nmn'45'unit_514 | C_nmn'45'void_516 | C_nmn'45'int_518 |
    C_nmn'45'float_520 | C_nmn'45'str_522 | C_nmn'45'buffer_524 |
    C_nmn'45'prod_530 T_NoMuNu_512 T_NoMuNu_512 |
    C_nmn'45'sum_536 T_NoMuNu_512 T_NoMuNu_512 |
    C_nmn'45'fun_544 T_NoMuNu_512 T_NoMuNu_512 |
    C_nmn'45'eff_550 T_NoMuNu_512 T_NoMuNu_512
-- Once.Grammar.Convert.typeToGType-NoMuNu
d_typeToGType'45'NoMuNu_556 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_NoMuNu_512 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeToGType'45'NoMuNu_556 v0 v1
  = case coe v1 of
      C_nmn'45'unit_514
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_TUnit_10) erased
      C_nmn'45'void_516
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_TVoid_12) erased
      C_nmn'45'int_518
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_TInt_14) erased
      C_nmn'45'float_520
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_TFloat_16) erased
      C_nmn'45'str_522
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_TString_20) erased
      C_nmn'45'buffer_524
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_TBuffer_18) erased
      C_nmn'45'prod_530 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> let v8 = d_typeToGType'45'NoMuNu_556 (coe v6) (coe v4) in
                  coe
                    (let v9 = d_typeToGType'45'NoMuNu_556 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.C__'8855'__24 (coe v10)
                                           (coe v12))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nmn'45'sum_536 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> let v8 = d_typeToGType'45'NoMuNu_556 (coe v6) (coe v4) in
                  coe
                    (let v9 = d_typeToGType'45'NoMuNu_556 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.C__'8853'__26 (coe v10)
                                           (coe v12))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nmn'45'fun_544 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v7 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v10 v11
                      -> let v12 = d_typeToGType'45'NoMuNu_556 (coe v7) (coe v5) in
                         coe
                           (let v13 = d_typeToGType'45'NoMuNu_556 (coe v9) (coe v6) in
                            coe
                              (case coe v12 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                   -> case coe v13 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__22
                                                  (coe v14) (coe v10) (coe v16))
                                               erased
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nmn'45'eff_550 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> let v9 = d_typeToGType'45'NoMuNu_556 (coe v6) (coe v4) in
                  coe
                    (let v10 = d_typeToGType'45'NoMuNu_556 (coe v8) (coe v5) in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                            -> case coe v10 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.C_TEff_28 (coe v11) (coe v13))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
