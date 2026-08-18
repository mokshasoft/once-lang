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
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeProdTailWF'45'irr_70 = erased
-- Once.Grammar.ParserBridge.parseTypeSumTailWF-irr
d_parseTypeSumTailWF'45'irr_88 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeSumTailWF'45'irr_88 = erased
-- Once.Grammar.ParserBridge.parseArrowTailWF-irr
d_parseArrowTailWF'45'irr_106 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
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
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeProdTail'45'as'45'strippedWF_162 = erased
-- Once.Grammar.ParserBridge.parseTypeSumTail-as-strippedWF
d_parseTypeSumTail'45'as'45'strippedWF_176 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseTypeSumTail'45'as'45'strippedWF_176 = erased
-- Once.Grammar.ParserBridge.parseArrowTail-as-strippedWF
d_parseArrowTail'45'as'45'strippedWF_190 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseArrowTail'45'as'45'strippedWF_190 = erased
-- Once.Grammar.ParserBridge.complete-atomWFraw
d_complete'45'atomWFraw_210 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'atomWFraw_210 v0 v1 v2 v3 ~v4
  = du_complete'45'atomWFraw_210 v0 v1 v2 v3
du_complete'45'atomWFraw_210 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'atomWFraw_210 v0 v1 v2 v3
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
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'buffer_138)
             erased
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'string_142
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'string_142)
             erased
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'eff_154 v5 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
                      -> let v16
                               = coe
                                   du_complete'45'atomWFraw_210 (coe v12) (coe v13) (coe v5)
                                   (coe v9) in
                         coe
                           (case coe v16 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                -> let v19
                                         = coe
                                             du_complete'45'atomWFraw_210 (coe v5) (coe v15)
                                             (coe v2) (coe v10) in
                                   coe
                                     (case coe v19 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'eff_154
                                                  v5 v17 v20)
                                               erased
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'io_162 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
                      -> let v13
                               = coe
                                   du_complete'45'atomWFraw_210 (coe v9) (coe v12) (coe v2)
                                   (coe v7) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'io_162 v14)
                                     erased
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_172 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe
                            du_complete'45'typeWFraw_300 (coe v11) (coe v1)
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
                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'paren_172
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                 v13)
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'mu_180 v7
        -> case coe v0 of
             (:) v8 v9
               -> let v10
                        = coe du_complete'45'functorSumWFraw_358 (coe v9) (coe v7) in
                  coe
                    (case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pa'45'mu_180 v11)
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-prodWFraw
d_complete'45'prodWFraw_224 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProd_98 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'prodWFraw_224 v0 ~v1 ~v2 v3 ~v4
  = du_complete'45'prodWFraw_224 v0 v3
du_complete'45'prodWFraw_224 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProd_98 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'prodWFraw_224 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192 v3 v5 v7 v8
        -> let v9
                 = coe
                     du_complete'45'atomWFraw_210 (coe v0) (coe v5) (coe v3) (coe v7) in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> let v12
                           = coe du_complete'45'prodTailWFraw_240 (coe v3) (coe v8) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192 v3 v5 v10
                                    v13)
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-prodTailWFraw
d_complete'45'prodTailWFraw_240 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProdTail_100 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'prodTailWFraw_240 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_complete'45'prodTailWFraw_240 v1 v4
du_complete'45'prodTailWFraw_240 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesProdTail_100 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'prodTailWFraw_240 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198 v4
        -> case coe v0 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    erased
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'done_198
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'star_212 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe
                            du_complete'45'atomWFraw_210 (coe v11) (coe v6) (coe v4)
                            (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> let v15
                                  = coe du_complete'45'prodTailWFraw_240 (coe v4) (coe v9) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Parser.TypeRelation.C_ppt'45'star_212
                                           v4 v6 v13 v16)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-sumWFraw
d_complete'45'sumWFraw_254 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSum_102 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'sumWFraw_254 v0 ~v1 ~v2 v3 ~v4
  = du_complete'45'sumWFraw_254 v0 v3
du_complete'45'sumWFraw_254 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSum_102 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'sumWFraw_254 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224 v3 v5 v7 v8
        -> let v9 = coe du_complete'45'prodWFraw_224 (coe v0) (coe v7) in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> let v12
                           = coe du_complete'45'sumTailWFraw_270 (coe v3) (coe v8) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224 v3 v5 v10
                                    v13)
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-sumTailWFraw
d_complete'45'sumTailWFraw_270 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSumTail_104 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'sumTailWFraw_270 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_complete'45'sumTailWFraw_270 v1 v4
du_complete'45'sumTailWFraw_270 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesSumTail_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'sumTailWFraw_270 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230 v4
        -> case coe v0 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    erased
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'done_230
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'plus_244 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> let v12 = coe du_complete'45'prodWFraw_224 (coe v11) (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> let v15
                                  = coe du_complete'45'sumTailWFraw_270 (coe v4) (coe v9) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Parser.TypeRelation.C_pst'45'plus_244
                                           v4 v6 v13 v16)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-arrowTailWFraw
d_complete'45'arrowTailWFraw_286 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesArrowTail_108 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'arrowTailWFraw_286 ~v0 v1 v2 v3 v4 ~v5
  = du_complete'45'arrowTailWFraw_286 v1 v2 v3 v4
du_complete'45'arrowTailWFraw_286 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesArrowTail_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'arrowTailWFraw_286 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262 v6
        -> case coe v0 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    erased
             (:) v7 v8
               -> coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'done_262
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_274 v9
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
                                         (let v19
                                                = coe
                                                    du_complete'45'typeWFraw_300 (coe v13) (coe v16)
                                                    (coe v2) (coe v9) in
                                          coe
                                            (case coe v19 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow'45'g_274
                                                         v20)
                                                      erased
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow_284 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
                      -> let v14
                               = coe
                                   du_complete'45'typeWFraw_300 (coe v10) (coe v13) (coe v2)
                                   (coe v8) in
                         coe
                           (case coe v14 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pat'45'arrow_284
                                        v15)
                                     erased
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-typeWFraw
d_complete'45'typeWFraw_300 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'typeWFraw_300 v0 v1 v2 v3 ~v4
  = du_complete'45'typeWFraw_300 v0 v1 v2 v3
du_complete'45'typeWFraw_300 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'typeWFraw_300 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256 v5 v7 v9 v10
        -> let v11 = coe du_complete'45'sumWFraw_254 (coe v0) (coe v9) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> let v14
                           = coe
                               du_complete'45'arrowTailWFraw_286 (coe v5) (coe v1) (coe v2)
                               (coe v10) in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256 v5 v7 v12
                                    v15)
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-functorAtomWFraw
d_complete'45'functorAtomWFraw_314 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorAtom_110 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'functorAtomWFraw_314 v0 v1 v2 v3 ~v4
  = du_complete'45'functorAtomWFraw_314 v0 v1 v2 v3
du_complete'45'functorAtomWFraw_314 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorAtom_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'functorAtomWFraw_314 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'id_288
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'id_288) erased
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'k_296 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v10
                      -> let v11
                               = coe
                                   du_complete'45'atomWFraw_210 (coe v9) (coe v10) (coe v2)
                                   (coe v7) in
                         coe
                           (case coe v11 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'k_296 v12)
                                     erased
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'paren_306 v5 v8
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe du_complete'45'functorSumWFraw_358 (coe v11) (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pfa'45'paren_306
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                 v13)
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-functorProdWFraw
d_complete'45'functorProdWFraw_328 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProd_112 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'functorProdWFraw_328 v0 ~v1 ~v2 v3 ~v4
  = du_complete'45'functorProdWFraw_328 v0 v3
du_complete'45'functorProdWFraw_328 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProd_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'functorProdWFraw_328 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfp'45'mk_318 v3 v5 v7 v8
        -> let v9
                 = coe
                     du_complete'45'functorAtomWFraw_314 (coe v0) (coe v5) (coe v3)
                     (coe v7) in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> let v12
                           = coe du_complete'45'functorProdTailWFraw_344 (coe v3) (coe v8) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pfp'45'mk_318 v3 v5 v10
                                    v13)
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-functorProdTailWFraw
d_complete'45'functorProdTailWFraw_344 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProdTail_114 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'functorProdTailWFraw_344 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_complete'45'functorProdTailWFraw_344 v1 v4
du_complete'45'functorProdTailWFraw_344 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorProdTail_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'functorProdTailWFraw_344 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324 v4
        -> case coe v0 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    erased
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'done_324
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'star_338 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe
                            du_complete'45'functorAtomWFraw_314 (coe v11) (coe v6) (coe v4)
                            (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> let v15
                                  = coe du_complete'45'functorProdTailWFraw_344 (coe v4) (coe v9) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Parser.TypeRelation.C_pfpt'45'star_338
                                           v4 v6 v13 v16)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-functorSumWFraw
d_complete'45'functorSumWFraw_358 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSum_116 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'functorSumWFraw_358 v0 ~v1 ~v2 v3 ~v4
  = du_complete'45'functorSumWFraw_358 v0 v3
du_complete'45'functorSumWFraw_358 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSum_116 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'functorSumWFraw_358 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfs'45'mk_350 v3 v5 v7 v8
        -> let v9
                 = coe du_complete'45'functorProdWFraw_328 (coe v0) (coe v7) in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> let v12
                           = coe du_complete'45'functorSumTailWFraw_374 (coe v3) (coe v8) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pfs'45'mk_350 v3 v5 v10
                                    v13)
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-functorSumTailWFraw
d_complete'45'functorSumTailWFraw_374 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSumTail_118 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'functorSumTailWFraw_374 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_complete'45'functorSumTailWFraw_374 v1 v4
du_complete'45'functorSumTailWFraw_374 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesFunctorSumTail_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'functorSumTailWFraw_374 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356 v4
        -> case coe v0 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    erased
             (:) v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'done_356
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'plus_370 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe du_complete'45'functorProdWFraw_328 (coe v11) (coe v8) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> let v15
                                  = coe du_complete'45'functorSumTailWFraw_374 (coe v4) (coe v9) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Parser.TypeRelation.C_pfst'45'plus_370
                                           v4 v6 v13 v16)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ParserBridge.complete-atom
d_complete'45'atom_1070 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_1070 = erased
-- Once.Grammar.ParserBridge.complete-type
d_complete'45'type_1094 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_1094 = erased
-- Once.Grammar.ParserBridge.stripType-inv
d_stripType'45'inv_1122 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripType'45'inv_1122 ~v0 v1 ~v2 ~v3 ~v4
  = du_stripType'45'inv_1122 v1
du_stripType'45'inv_1122 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripType'45'inv_1122 v0
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
d_stripAtom'45'inv_1144 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stripAtom'45'inv_1144 ~v0 v1 ~v2 ~v3 ~v4
  = du_stripAtom'45'inv_1144 v1
du_stripAtom'45'inv_1144 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stripAtom'45'inv_1144 v0
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
d_sound'45'type_1162 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
d_sound'45'type_1162 v0 ~v1 ~v2 ~v3 = du_sound'45'type_1162 v0
du_sound'45'type_1162 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
du_sound'45'type_1162 v0
  = let v1
          = coe
              du_stripType'45'inv_1122
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
                                                 MAlonzo.Code.Once.Parser.Type.du_parseTypeProdTailWF_148
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
                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192
                                                                         v5 v3 v6 v12 in
                                                               coe
                                                                 (let v14
                                                                        = coe
                                                                            MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_154
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
                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                                                    v11
                                                                                                    v9
                                                                                                    v13
                                                                                                    v19 in
                                                                                          coe
                                                                                            (let v21
                                                                                                   = coe
                                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
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
                                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
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
                                                                                                           MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
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
                                                                                MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_154
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
                                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                                                        v11
                                                                                                        v9
                                                                                                        v12
                                                                                                        v18 in
                                                                                              coe
                                                                                                (let v20
                                                                                                       = coe
                                                                                                           MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
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
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                           -> case coe
                                                                                                     v16 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                  -> let v19
                                                                                                           = coe
                                                                                                               MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
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
                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
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
                                           -> let v7
                                                    = coe
                                                        MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_154
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
                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                                v5 v3 v6 v12 in
                                                                      coe
                                                                        (let v14
                                                                               = coe
                                                                                   MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
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
                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
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
                                                  -> let v7
                                                           = coe
                                                               MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
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
                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
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
d_sound'45'atom_1184 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96
d_sound'45'atom_1184 v0 ~v1 ~v2 ~v3 = du_sound'45'atom_1184 v0
du_sound'45'atom_1184 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesAtom_96
du_sound'45'atom_1184 v0
  = let v1
          = coe
              du_stripAtom'45'inv_1144
              (coe
                 MAlonzo.Code.Once.Parser.Type.du_parseTypeAtomWF_130 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
