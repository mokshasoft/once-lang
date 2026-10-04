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

module MAlonzo.Code.Once.Grammar.ParserBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Type

-- Once.Grammar.ParserBridge.parseTypeAtomWF-irr
d_parseTypeAtomWF'45'irr_12 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeAtomWF'45'irr_12 = erased
-- Once.Grammar.ParserBridge.parseTypeWF-irr
d_parseTypeWF'45'irr_26 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeWF'45'irr_26 = erased
-- Once.Grammar.ParserBridge.parseTypeSumWF-irr
d_parseTypeSumWF'45'irr_40 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeSumWF'45'irr_40 = erased
-- Once.Grammar.ParserBridge.parseTypeProdWF-irr
d_parseTypeProdWF'45'irr_54 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeProdWF'45'irr_54 = erased
-- Once.Grammar.ParserBridge.parseTypeProdTailWF-irr
d_parseTypeProdTailWF'45'irr_70 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeProdTailWF'45'irr_70 = erased
-- Once.Grammar.ParserBridge.parseTypeSumTailWF-irr
d_parseTypeSumTailWF'45'irr_88 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeSumTailWF'45'irr_88 = erased
-- Once.Grammar.ParserBridge.parseArrowTailWF-irr
d_parseArrowTailWF'45'irr_106 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseArrowTailWF'45'irr_106 = erased
-- Once.Grammar.ParserBridge.parseType-as-strippedWF
d_parseType'45'as'45'strippedWF_120 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'as'45'strippedWF_120 = erased
-- Once.Grammar.ParserBridge.parseTypeAtom-as-strippedWF
d_parseTypeAtom'45'as'45'strippedWF_130 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeAtom'45'as'45'strippedWF_130 = erased
-- Once.Grammar.ParserBridge.parseTypeSum-as-strippedWF
d_parseTypeSum'45'as'45'strippedWF_140 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeSum'45'as'45'strippedWF_140 = erased
-- Once.Grammar.ParserBridge.parseTypeProd-as-strippedWF
d_parseTypeProd'45'as'45'strippedWF_150 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeProd'45'as'45'strippedWF_150 = erased
-- Once.Grammar.ParserBridge.parseTypeProdTail-as-strippedWF
d_parseTypeProdTail'45'as'45'strippedWF_162 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeProdTail'45'as'45'strippedWF_162 = erased
-- Once.Grammar.ParserBridge.parseTypeSumTail-as-strippedWF
d_parseTypeSumTail'45'as'45'strippedWF_176 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeSumTail'45'as'45'strippedWF_176 = erased
-- Once.Grammar.ParserBridge.parseArrowTail-as-strippedWF
d_parseArrowTail'45'as'45'strippedWF_190 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseArrowTail'45'as'45'strippedWF_190 = erased
-- Once.Grammar.ParserBridge.fAtomEff
d_fAtomEff_202 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fAtomEff_202 = erased
-- Once.Grammar.ParserBridge.fProdEff
d_fProdEff_212 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fProdEff_212 = erased
-- Once.Grammar.ParserBridge.fSumEff
d_fSumEff_226 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSumEff_226 = erased
-- Once.Grammar.ParserBridge.fAtomParenEff
d_fAtomParenEff_240 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fAtomParenEff_240 = erased
-- Once.Grammar.ParserBridge.fProdParenEff
d_fProdParenEff_254 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fProdParenEff_254 = erased
-- Once.Grammar.ParserBridge.fSumParenEff
d_fSumParenEff_268 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSumParenEff_268 = erased
-- Once.Grammar.ParserBridge.complete-atomWFraw
d_complete'45'atomWFraw_290 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'atomWFraw_290 v0 v1 v2 v3 ~v4
  = du_complete'45'atomWFraw_290 v0 v1 v2 v3
du_complete'45'atomWFraw_290 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'atomWFraw_290 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'unit_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'unit_122) erased
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'void_126
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'void_126) erased
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'int_130
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'int_130) erased
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'float_134)
             erased
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'eff_146 v5 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
                      -> let v16
                               = coe
                                   du_complete'45'atomWFraw_290 (coe v12) (coe v13) (coe v5)
                                   (coe v9) in
                         coe
                           (case coe v16 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                -> let v19
                                         = coe
                                             du_complete'45'atomWFraw_290 (coe v5) (coe v15)
                                             (coe v2) (coe v10) in
                                   coe
                                     (case coe v19 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'eff_146
                                                  v5 v17 v20)
                                               erased
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'io_154 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v10 v11 v12
                      -> let v13
                               = coe
                                   du_complete'45'atomWFraw_290 (coe v9) (coe v12) (coe v2)
                                   (coe v7) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'io_154 v14)
                                     erased
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_164 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe
                            du_complete'45'typeWFraw_380 (coe v11) (coe v1)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                            (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_164
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                 v13)
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'mu_172 v7
        -> case coe v0 of
             (:) v8 v9
               -> let v10
                        = coe du_complete'45'functorSumWFraw_438 (coe v9) (coe v7) in
                  coe
                    (case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'mu_172 v11)
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'nu_180 v7
        -> case coe v0 of
             (:) v8 v9
               -> let v10
                        = coe du_complete'45'functorSumWFraw_438 (coe v9) (coe v7) in
                  coe
                    (case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'nu_180 v11)
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'nu'45'eff_188 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v9 of
                    (:) v10 v11
                      -> case coe v11 of
                           (:) v12 v13
                             -> let v14
                                      = coe du_complete'45'functorSumWFraw_438 (coe v13) (coe v7) in
                                coe
                                  (case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'nu'45'eff_188
                                               v15)
                                            erased
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-prodWFraw
d_complete'45'prodWFraw_304 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProd_98 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'prodWFraw_304 v0 ~v1 ~v2 v3 ~v4
  = du_complete'45'prodWFraw_304 v0 v3
du_complete'45'prodWFraw_304 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProd_98 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'prodWFraw_304 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_200 v3 v5 v7 v8
        -> let v9
                 = coe
                     du_complete'45'atomWFraw_290 (coe v0) (coe v5) (coe v3) (coe v7) in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> let v12
                           = coe du_complete'45'prodTailWFraw_320 (coe v3) (coe v8) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_200 v3 v5 v10
                                    v13)
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-prodTailWFraw
d_complete'45'prodTailWFraw_320 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProdTail_100 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'prodTailWFraw_320 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_complete'45'prodTailWFraw_320 v1 v4
du_complete'45'prodTailWFraw_320 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProdTail_100 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'prodTailWFraw_320 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_206 v4
        -> case coe v0 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_206
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    erased
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_206
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'star_220 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe
                            du_complete'45'atomWFraw_290 (coe v11) (coe v6) (coe v4)
                            (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> let v15
                                  = coe du_complete'45'prodTailWFraw_320 (coe v4) (coe v9) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'star_220
                                           v4 v6 v13 v16)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-sumWFraw
d_complete'45'sumWFraw_334 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSum_102 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'sumWFraw_334 v0 ~v1 ~v2 v3 ~v4
  = du_complete'45'sumWFraw_334 v0 v3
du_complete'45'sumWFraw_334 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSum_102 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'sumWFraw_334 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_232 v3 v5 v7 v8
        -> let v9 = coe du_complete'45'prodWFraw_304 (coe v0) (coe v7) in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> let v12
                           = coe du_complete'45'sumTailWFraw_350 (coe v3) (coe v8) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_232 v3 v5 v10
                                    v13)
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-sumTailWFraw
d_complete'45'sumTailWFraw_350 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSumTail_104 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'sumTailWFraw_350 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_complete'45'sumTailWFraw_350 v1 v4
du_complete'45'sumTailWFraw_350 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSumTail_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'sumTailWFraw_350 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_238 v4
        -> case coe v0 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_238
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    erased
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_238
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'plus_252 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> let v12 = coe du_complete'45'prodWFraw_304 (coe v11) (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> let v15
                                  = coe du_complete'45'sumTailWFraw_350 (coe v4) (coe v9) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'plus_252
                                           v4 v6 v13 v16)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-arrowTailWFraw
d_complete'45'arrowTailWFraw_366 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesArrowTail_108 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'arrowTailWFraw_366 ~v0 v1 v2 v3 v4 ~v5
  = du_complete'45'arrowTailWFraw_366 v1 v2 v3 v4
du_complete'45'arrowTailWFraw_366 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesArrowTail_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'arrowTailWFraw_366 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_270 v6
        -> case coe v0 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_270
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    erased
             (:) v7 v8
               -> coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_270
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_282 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v11 of
                    (:) v12 v13
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v14 v15 v16
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                    -> coe
                                         seq (coe v17)
                                         (let v19
                                                = coe
                                                    du_complete'45'typeWFraw_380 (coe v13) (coe v16)
                                                    (coe v2) (coe v9) in
                                          coe
                                            (case coe v19 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_282
                                                         v20)
                                                      erased
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow_292 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v11 v12 v13
                      -> let v14
                               = coe
                                   du_complete'45'typeWFraw_380 (coe v10) (coe v13) (coe v2)
                                   (coe v8) in
                         coe
                           (case coe v14 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow_292
                                        v15)
                                     erased
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-typeWFraw
d_complete'45'typeWFraw_380 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'typeWFraw_380 v0 v1 v2 v3 ~v4
  = du_complete'45'typeWFraw_380 v0 v1 v2 v3
du_complete'45'typeWFraw_380 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'typeWFraw_380 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264 v5 v7 v9 v10
        -> let v11 = coe du_complete'45'sumWFraw_334 (coe v0) (coe v9) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> let v14
                           = coe
                               du_complete'45'arrowTailWFraw_366 (coe v5) (coe v1) (coe v2)
                               (coe v10) in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264 v5 v7 v12
                                    v15)
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-functorAtomWFraw
d_complete'45'functorAtomWFraw_394 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorAtom_110 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'functorAtomWFraw_394 v0 v1 v2 v3 ~v4
  = du_complete'45'functorAtomWFraw_394 v0 v1 v2 v3
du_complete'45'functorAtomWFraw_394 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorAtom_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'functorAtomWFraw_394 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'id_296
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'id_296) erased
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'k_304 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_112 v10
                      -> let v11
                               = coe
                                   du_complete'45'atomWFraw_290 (coe v9) (coe v10) (coe v2)
                                   (coe v7) in
                         coe
                           (case coe v11 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'k_304 v12)
                                     erased
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'paren_314 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe du_complete'45'functorSumWFraw_438 (coe v11) (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'paren_314
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                 v13)
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-functorProdWFraw
d_complete'45'functorProdWFraw_408 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProd_112 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'functorProdWFraw_408 v0 ~v1 ~v2 v3 ~v4
  = du_complete'45'functorProdWFraw_408 v0 v3
du_complete'45'functorProdWFraw_408 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProd_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'functorProdWFraw_408 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfp'45'mk_326 v3 v5 v7 v8
        -> let v9
                 = coe
                     du_complete'45'functorAtomWFraw_394 (coe v0) (coe v5) (coe v3)
                     (coe v7) in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> let v12
                           = coe du_complete'45'functorProdTailWFraw_424 (coe v3) (coe v8) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pfp'45'mk_326 v3 v5 v10
                                    v13)
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-functorProdTailWFraw
d_complete'45'functorProdTailWFraw_424 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProdTail_114 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'functorProdTailWFraw_424 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_complete'45'functorProdTailWFraw_424 v1 v4
du_complete'45'functorProdTailWFraw_424 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProdTail_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'functorProdTailWFraw_424 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_332 v4
        -> case coe v0 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_332
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    erased
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_332
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'star_346 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe
                            du_complete'45'functorAtomWFraw_394 (coe v11) (coe v6) (coe v4)
                            (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> let v15
                                  = coe du_complete'45'functorProdTailWFraw_424 (coe v4) (coe v9) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'star_346
                                           v4 v6 v13 v16)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-functorSumWFraw
d_complete'45'functorSumWFraw_438 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSum_116 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'functorSumWFraw_438 v0 ~v1 ~v2 v3 ~v4
  = du_complete'45'functorSumWFraw_438 v0 v3
du_complete'45'functorSumWFraw_438 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSum_116 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'functorSumWFraw_438 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfs'45'mk_358 v3 v5 v7 v8
        -> let v9
                 = coe du_complete'45'functorProdWFraw_408 (coe v0) (coe v7) in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> let v12
                           = coe du_complete'45'functorSumTailWFraw_454 (coe v3) (coe v8) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pfs'45'mk_358 v3 v5 v10
                                    v13)
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-functorSumTailWFraw
d_complete'45'functorSumTailWFraw_454 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSumTail_118 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'functorSumTailWFraw_454 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_complete'45'functorSumTailWFraw_454 v1 v4
du_complete'45'functorSumTailWFraw_454 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSumTail_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'functorSumTailWFraw_454 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_364 v4
        -> case coe v0 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_364
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    erased
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_364
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'plus_378 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe du_complete'45'functorProdWFraw_408 (coe v11) (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> let v15
                                  = coe du_complete'45'functorSumTailWFraw_454 (coe v4) (coe v9) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'plus_378
                                           v4 v6 v13 v16)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-atom
d_complete'45'atom_1194 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_1194 = erased
-- Once.Grammar.ParserBridge.complete-type
d_complete'45'type_1218 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_1218 = erased
-- Once.Grammar.ParserBridge.stripType-inv
d_stripType'45'inv_1246 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripType'45'inv_1246 ~v0 v1 ~v2 ~v3 ~v4
  = du_stripType'45'inv_1246 v1
du_stripType'45'inv_1246 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripType'45'inv_1246 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.stripAtom-inv
d_stripAtom'45'inv_1268 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripAtom'45'inv_1268 ~v0 v1 ~v2 ~v3 ~v4
  = du_stripAtom'45'inv_1268 v1
du_stripAtom'45'inv_1268 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripAtom'45'inv_1268 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.sound-type
d_sound'45'type_1286 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
d_sound'45'type_1286 v0 ~v1 ~v2 ~v3 = du_sound'45'type_1286 v0
du_sound'45'type_1286 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
du_sound'45'type_1286 v0
  = let v1
          = coe
              du_stripType'45'inv_1246
              (let v1
                     = coe
                         MAlonzo.Code.Once.Parser.Type.du_parseTypeAtomWF_130 (coe v0) in
               coe
                 (case coe v1 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                    -> let v7
                                             = coe
                                                 MAlonzo.Code.Once.Parser.Type.du_parseTypeProdTailWF_152
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
                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_200
                                                                         v5 v3 v6 v12 in
                                                               coe
                                                                 (let v14
                                                                        = coe
                                                                            MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_158
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
                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_232
                                                                                                    v11
                                                                                                    v9
                                                                                                    v13
                                                                                                    v19 in
                                                                                          coe
                                                                                            (let v21
                                                                                                   = coe
                                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
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
                                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
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
                                                                                                           MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
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
                                                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
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
                                                                                MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_158
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
                                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_232
                                                                                                        v11
                                                                                                        v9
                                                                                                        v12
                                                                                                        v18 in
                                                                                              coe
                                                                                                (let v20
                                                                                                       = coe
                                                                                                           MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
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
                                                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
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
                                                                                                               MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
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
                                                                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
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
                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
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
                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
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
                                                        MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_158
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
                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_232
                                                                                v5 v3 v6 v12 in
                                                                      coe
                                                                        (let v14
                                                                               = coe
                                                                                   MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
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
                                                                                                            MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
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
                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
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
                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
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
                                                               MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
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
                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
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
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Grammar.ParserBridge.sound-atom
d_sound'45'atom_1308 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96
d_sound'45'atom_1308 v0 ~v1 ~v2 ~v3 = du_sound'45'atom_1308 v0
du_sound'45'atom_1308 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96
du_sound'45'atom_1308 v0
  = let v1
          = coe
              du_stripAtom'45'inv_1268
              (coe
                 MAlonzo.Code.Once.Parser.Type.du_parseTypeAtomWF_130 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
