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

module MAlonzo.Code.Once.Parser.Module where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.DeclTail
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Body
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Def
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.OpDecl
import qualified MAlonzo.Code.Once.Parser.Module.Import
import qualified MAlonzo.Code.Once.Parser.PolyType
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Module.pdb-sub
d_pdb'45'sub_10 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdb'45'sub_10 ~v0 v1 v2 = du_pdb'45'sub_10 v1 v2
du_pdb'45'sub_10 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pdb'45'sub_10 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0) (coe v6)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du_foldr_216
                                             (let v7
                                                    = \ v7 ->
                                                        addInt (coe (1 :: Integer)) (coe v7) in
                                              coe (coe (\ v8 -> v7)))
                                             (coe (0 :: Integer)) (coe v0)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.pdb-fb-sig-go
d_pdb'45'fb'45'sig'45'go_36 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdb'45'fb'45'sig'45'go_36 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      else coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 (coe v0)
                   (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                   (coe
                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                         (coe
                            MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                            (coe v4)
                            (coe
                               MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1'45''8804'_308
                               (coe v1)))))))
-- Once.Parser.Module.pdb-fb-sig
d_pdb'45'fb'45'sig_62 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdb'45'fb'45'sig_62 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           d_pdb'45'fb'45'sig'45'go_36 (coe v0) (coe v1) (coe v4) (coe v6)
                           (coe v7)
                           (coe
                              MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_eqHead_10 (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.pdb-fb-go
d_pdb'45'fb'45'go_82 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdb'45'fb'45'go_82 v0 v1 v2
  = if coe v2
      then coe
             d_pdb'45'fb'45'sig_62 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.PolyType.d_parsePolyTypeB_558
                (coe
                   MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302 (coe v1)))
      else coe
             du_pdb'45'sub_10 (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.Module.FunDef.Def.d_parseFunDefB_12
                (coe v0) (coe v1))
-- Once.Parser.Module.pdb-fb
d_pdb'45'fb_96 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdb'45'fb_96 v0 v1
  = coe
      d_pdb'45'fb'45'go_82 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.Module.DeclTail.d_colonHead_300 (coe v1))
-- Once.Parser.Module.pdb-kw3
d_pdb'45'kw3_106 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdb'45'kw3_106 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       du_pdb'45'sub_10 (coe v1)
                       (coe
                          MAlonzo.Code.Once.Parser.Module.DeclTail.d_parseSignatureB_372
                          (coe v1)))
             else coe seq (coe v4) (coe d_pdb'45'fb_96 (coe v0) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.pdb-kw2
d_pdb'45'kw2_120 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdb'45'kw2_120 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       du_pdb'45'sub_10 (coe v1)
                       (coe
                          MAlonzo.Code.Once.Parser.Module.DeclTail.d_parseTypeAliasB_174
                          (coe v1)))
             else coe
                    seq (coe v4)
                    (coe
                       d_pdb'45'kw3_106 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                          (coe ("signature" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.pdb-kw1
d_pdb'45'kw1_134 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdb'45'kw1_134 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       du_pdb'45'sub_10 (coe v1)
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Import.d_parseImportB_270
                          (coe v1)))
             else coe
                    seq (coe v4)
                    (coe
                       d_pdb'45'kw2_120 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                          (coe ("type" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.parseDeclB
d_parseDeclB_146 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseDeclB_146 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
                  -> coe
                       d_pdb'45'kw1_134 (coe v4) (coe v3)
                       (coe
                          MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v4)
                          (coe ("import" :: Data.Text.Text)))
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                  -> coe
                       MAlonzo.Code.Once.Parser.Module.FunDef.OpDecl.d_tryOpDeclB_96
                       (coe v0)
                _ -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.parseDecl
d_parseDecl_154 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseDecl_154 v0
  = let v1 = d_parseDeclB_146 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.skipNewlines-≤
d_skipNewlines'45''8804'_176 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_skipNewlines'45''8804'_176 v0 ~v1 ~v2 ~v3
  = du_skipNewlines'45''8804'_176 v0
du_skipNewlines'45''8804'_176 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_skipNewlines'45''8804'_176 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Parser.Token.C_TWord_8 v3
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TInt_10 v3
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v3 v4 v5
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TString_14 v3
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TRParen_18
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TColon_24
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TEquals_26
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TArrow_28
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TLambda_36
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TComma_38
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TAt_42
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TPipe_44
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TDot_46
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TPlus_48
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TMinus_50
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TStar_52
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TSlash_54
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TPercent_56
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TLt_60
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TLe_62
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TGt_64
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TGe_66
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TNeq_70
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TBang_72
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             MAlonzo.Code.Once.Parser.Token.C_TNewline_74
               -> let v3
                        = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278 (coe v2) in
                  coe
                    (let v4
                           = \ v4 v5 v6 -> coe du_skipNewlines'45''8804'_176 (coe v2) in
                     coe
                       (case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                   -> coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                        (coe v4 v6 v7 erased)
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                           (coe
                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                              (coe
                                                 (\ v8 v9 -> addInt (coe (1 :: Integer)) (coe v9)))
                                              (coe (0 :: Integer)) (coe v2)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (coe (\ v5 v6 -> addInt (coe (1 :: Integer)) (coe v6)))
                                    (coe (0 :: Integer)) (coe v2))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             MAlonzo.Code.Once.Parser.Token.C_TEOF_76
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.pdwf-dc
d_pdwf'45'dc_292 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdwf'45'dc_292 ~v0 ~v1 v2 v3 v4 = du_pdwf'45'dc_292 v2 v3 v4
du_pdwf'45'dc_292 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pdwf'45'dc_292 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_parseDeclsWF_316 (coe v6))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe du_parseDeclsWF_316 (coe v6))))
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe du_parseDeclsWF_316 (coe v6))))
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                       (coe v7))
                                    (coe v1))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.pdwf-sk
d_pdwf'45'sk_308 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdwf'45'sk_308 v0 ~v1 v2 v3 = du_pdwf'45'sk_308 v0 v2 v3
du_pdwf'45'sk_308 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pdwf'45'sk_308 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_pdwf'45'dc_292 (coe v5) (coe v2 v4 v5 erased)
                    (coe d_parseDeclB_146 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                   (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.parseDeclsWF
d_parseDeclsWF_316 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseDeclsWF_316 v0 ~v1 = du_parseDeclsWF_316 v0
du_parseDeclsWF_316 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseDeclsWF_316 v0
  = coe
      du_pdwf'45'sk_308 (coe v0)
      (coe MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278 (coe v0))
      (\ v1 v2 v3 -> coe du_skipNewlines'45''8804'_176 (coe v0))
-- Once.Parser.Module.parseDecls
d_parseDecls_362 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseDecls_362 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_r_370 (coe v0)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_r_370 (coe v0)))))
-- Once.Parser.Module._.r
d_r_370 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_r_370 v0 = coe du_parseDeclsWF_316 (coe v0)
-- Once.Parser.Module.parseModule-pd
d_parseModule'45'pd_372 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseModule'45'pd_372 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v3))
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.parseModule
d_parseModule_380 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseModule_380 v0
  = coe
      d_parseModule'45'pd_372 (coe d_parseDecls_362 (coe v0)) (coe v0)
