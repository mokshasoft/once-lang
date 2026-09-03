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

module MAlonzo.Code.Once.Grammar.OpDeclBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Grammar.FunDefBridge
import qualified MAlonzo.Code.Once.Grammar.PolyTypeBridge
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.PolyInst
import qualified MAlonzo.Code.Once.Parser.Module.Alloc
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.DeclTail
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Body
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Def
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.OpDecl
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Params
import qualified MAlonzo.Code.Once.Parser.Module.OpName
import qualified MAlonzo.Code.Once.Parser.PolyType
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Grammar.OpDecl

-- Once.Grammar.OpDeclBridge.sound-opChars
d_sound'45'opChars_16 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpChars_8
d_sound'45'opChars_16 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'opChars_16 v0 v1
du_sound'45'opChars_16 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpChars_8
du_sound'45'opChars_16 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> coe
             du_sound'45'pocGo_32 (coe v3) (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.Module.OpName.d_opTokClass_16 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.OpDeclBridge.sound-pocGo
d_sound'45'pocGo_32 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Once.Parser.Module.OpName.T_OpTok_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpChars_8
d_sound'45'pocGo_32 ~v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'pocGo_32 v1 v2 v3
du_sound'45'pocGo_32 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Once.Parser.Module.OpName.T_OpTok_8 ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpChars_8
du_sound'45'pocGo_32 v0 v1 v2
  = case coe v1 of
      []
        -> case coe v2 of
             MAlonzo.Code.Once.Parser.Module.OpName.C_otChar_12 v3
               -> let v4
                        = MAlonzo.Code.Once.Parser.Module.OpName.d_parseOpCharsB_58
                            (coe v0)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1)) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> coe
                                            MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_poc'45'char_32
                                            v3
                                            (coe
                                               du_sound'45'opChars_16 (coe v0)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe v3) (coe v1)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Parser.Module.OpName.C_otClose_10
               -> coe MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_poc'45'close_18
             MAlonzo.Code.Once.Parser.Module.OpName.C_otChar_12 v5
               -> let v6
                        = MAlonzo.Code.Once.Parser.Module.OpName.d_parseOpCharsB_58
                            (coe v0)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v1)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> case coe v9 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                       -> coe
                                            MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_poc'45'char_32
                                            v5
                                            (coe
                                               du_sound'45'opChars_16 (coe v0)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe v5) (coe v1)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.OpDeclBridge.complete-opChars
d_complete'45'opChars_158 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpChars_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'opChars_158 v0 ~v1 ~v2 v3 v4
  = du_complete'45'opChars_158 v0 v3 v4
du_complete'45'opChars_158 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpChars_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'opChars_158 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_poc'45'close_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                       coe (coe (\ v9 -> v8)))
                      (coe (0 :: Integer)) (coe v1))))
             erased
      MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_poc'45'char_32 v6 v10
        -> case coe v0 of
             (:) v11 v12
               -> let v13
                        = coe du_complete'45'opChars_158 (coe v12) (coe v1) (coe v10) in
                  coe
                    (case coe v13 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe MAlonzo.Code.Data.List.Base.du_length_268 v12) (coe v14)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (let v16
                                                 = \ v16 -> addInt (coe (1 :: Integer)) (coe v16) in
                                           coe (coe (\ v17 -> v16)))
                                          (coe (0 :: Integer)) (coe v12)))))
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.OpDeclBridge.sound-opAfter
d_sound'45'opAfter_200 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpAfter_36
d_sound'45'opAfter_200 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'opAfter_200 v0 v1
du_sound'45'opAfter_200 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpAfter_36
du_sound'45'opAfter_200 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Module.DeclTail.d_colonHead_300
              (coe v1) in
    coe
      (if coe v2
         then let v3
                    = coe
                        MAlonzo.Code.Once.Parser.PolyType.du_ppB'45'go_542
                        (coe
                           MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302 (coe v1))
                        (let v3
                               = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                         coe
                           (let v4
                                  = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                            coe
                              (let v5
                                     = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                               (coe v1) in
                                     coe
                                       (let v8
                                              = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_tvarP_46
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                     (coe v1)) in
                                        coe
                                          (case coe v8 of
                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                               -> case coe v9 of
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                      -> case coe v11 of
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                             -> let v14
                                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                          (coe v5) (coe v10)
                                                                          (coe v12) in
                                                                coe
                                                                  (case coe v14 of
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                       -> case coe v15 of
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                              -> let v18
                                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                           (coe v4)
                                                                                           (coe v16)
                                                                                           (coe
                                                                                              v17) in
                                                                                 coe
                                                                                   (case coe v18 of
                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                        -> case coe
                                                                                                  v19 of
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                    (coe
                                                                                                       v3)
                                                                                                    (coe
                                                                                                       v20)
                                                                                                    (coe
                                                                                                       v21)
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                        -> coe v18
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                       -> case coe v14 of
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                              -> case coe v15 of
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                     -> coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                          (coe v3)
                                                                                          (coe v16)
                                                                                          (coe v17)
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                              -> coe v14
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                               -> let v9
                                                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                            (coe v6) (coe v7) in
                                                  coe
                                                    (case coe v9 of
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                         -> case coe v10 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                -> let v13
                                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                             (coe v5) (coe v11)
                                                                             (coe v12) in
                                                                   coe
                                                                     (case coe v13 of
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                          -> case coe v14 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                 -> let v17
                                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                              (coe
                                                                                                 v4)
                                                                                              (coe
                                                                                                 v15)
                                                                                              (coe
                                                                                                 v16) in
                                                                                    coe
                                                                                      (case coe
                                                                                              v17 of
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                           -> case coe
                                                                                                     v18 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                  -> coe
                                                                                                       MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                       (coe
                                                                                                          v3)
                                                                                                       (coe
                                                                                                          v19)
                                                                                                       (coe
                                                                                                          v20)
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                           -> coe
                                                                                                v17
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                                 -> case coe v14 of
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                        -> coe
                                                                                             MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                             (coe
                                                                                                v3)
                                                                                             (coe
                                                                                                v15)
                                                                                             (coe
                                                                                                v16)
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                 -> coe v13
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         -> case coe v9 of
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                -> case coe v10 of
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                       -> let v13
                                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                    (coe v4)
                                                                                    (coe v11)
                                                                                    (coe v12) in
                                                                          coe
                                                                            (case coe v13 of
                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                                 -> case coe v14 of
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                        -> coe
                                                                                             MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                             (coe
                                                                                                v3)
                                                                                             (coe
                                                                                                v15)
                                                                                             (coe
                                                                                                v16)
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                 -> coe v13
                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                -> case coe v9 of
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                       -> case coe v10 of
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                              -> coe
                                                                                   MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                   (coe v3)
                                                                                   (coe v11)
                                                                                   (coe v12)
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                       -> coe v9
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                             _ -> MAlonzo.RTE.mazUnreachableError))))))) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> coe
                                 seq (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_poa'45'sig_46
                                    (coe
                                       MAlonzo.Code.Once.Grammar.PolyTypeBridge.du_parsePolyTypeB'45'sound_42
                                       (coe
                                          MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                          (coe v1))))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         else (let v3
                     = coe
                         MAlonzo.Code.Once.Parser.Module.FunDef.Def.du_pfd'45'body_52
                         (coe
                            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Parser.Module.FunDef.Params.du_pp'45'aw_58
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                 (coe v1)
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                    (coe v1))))))
                                     (coe
                                        MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                 (coe v1)
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                    (coe v1)
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                       (coe v1))))))))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                           (coe v1)))))))
                         (coe
                            MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_pfb'45'eq_34 (coe v0)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                        (coe v1)))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Once.Parser.Module.FunDef.Params.du_pp'45'aw_58
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                           (coe
                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                 (coe v1))))))
                                  (coe
                                     MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                 (coe v1)
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                    (coe v1)))))))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Parser.Module.FunDef.Params.du_pp'45'aw_58
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                 (coe v1)
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                    (coe v1))))))
                                     (coe
                                        MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                 (coe v1)
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                    (coe v1)
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                       (coe v1))))))))))
                            (coe
                               MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_eqHead_10
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        MAlonzo.Code.Once.Parser.Module.FunDef.Params.du_pp'45'aw_58
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                 (coe v1)
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                    (coe v1)
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                       (coe v1))))))
                                        (coe
                                           MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                    (coe v1)
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                       (coe v1)
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                          (coe v1)))))))))))) in
               coe
                 (case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                             -> coe
                                  seq (coe v6)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_poa'45'fun_54
                                     (coe
                                        MAlonzo.Code.Once.Grammar.FunDefBridge.du_sound'45'fundef_382
                                        (coe v0) (coe v1)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Grammar.OpDeclBridge.complete-opAfter
d_complete'45'opAfter_280 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpAfter_36 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'opAfter_280 ~v0 v1 ~v2 ~v3 v4
  = du_complete'45'opAfter_280 v1 v4
du_complete'45'opAfter_280 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpAfter_36 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'opAfter_280 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_poa'45'sig_46 v6
        -> let v7
                 = coe
                     MAlonzo.Code.Once.Grammar.PolyTypeBridge.du_ppB'45'go'45'complete_60
                     (coe
                        MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302 (coe v0))
                     (let v7
                            = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                      coe
                        (let v8
                               = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                         coe
                           (let v9
                                  = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                            coe
                              (let v10
                                     = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                               coe
                                 (let v11
                                        = MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                            (coe v0) in
                                  coe
                                    (let v12
                                           = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_tvarP_46
                                               (coe
                                                  MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                  (coe v0)) in
                                     coe
                                       (case coe v12 of
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                            -> case coe v13 of
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                   -> case coe v15 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                          -> let v18
                                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                       (coe v9) (coe v14)
                                                                       (coe v16) in
                                                             coe
                                                               (case coe v18 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                    -> case coe v19 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                           -> let v22
                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                        (coe v8)
                                                                                        (coe v20)
                                                                                        (coe v21) in
                                                                              coe
                                                                                (case coe v22 of
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                                     -> case coe
                                                                                               v23 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                            -> coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                 (coe
                                                                                                    v7)
                                                                                                 (coe
                                                                                                    v24)
                                                                                                 (coe
                                                                                                    v25)
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                     -> coe v22
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> case coe v18 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                           -> case coe v19 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                  -> coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                       (coe v7)
                                                                                       (coe v20)
                                                                                       (coe v21)
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                           -> coe v18
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            -> let v13
                                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                         (coe v10) (coe v11) in
                                               coe
                                                 (case coe v13 of
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                      -> case coe v14 of
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                             -> let v17
                                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                          (coe v9) (coe v15)
                                                                          (coe v16) in
                                                                coe
                                                                  (case coe v17 of
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                       -> case coe v18 of
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                              -> let v21
                                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                           (coe v8)
                                                                                           (coe v19)
                                                                                           (coe
                                                                                              v20) in
                                                                                 coe
                                                                                   (case coe v21 of
                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                                                                        -> case coe
                                                                                                  v22 of
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                    (coe
                                                                                                       v7)
                                                                                                    (coe
                                                                                                       v23)
                                                                                                    (coe
                                                                                                       v24)
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                        -> coe v21
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                       -> case coe v17 of
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                              -> case coe v18 of
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                     -> coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                          (coe v7)
                                                                                          (coe v19)
                                                                                          (coe v20)
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                              -> coe v17
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      -> case coe v13 of
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                             -> case coe v14 of
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                    -> let v17
                                                                             = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                 (coe v8) (coe v15)
                                                                                 (coe v16) in
                                                                       coe
                                                                         (case coe v17 of
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                              -> case coe v18 of
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                     -> coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                          (coe v7)
                                                                                          (coe v19)
                                                                                          (coe v20)
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                              -> coe v17
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                             -> case coe v13 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                    -> case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                           -> coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                (coe v7) (coe v15)
                                                                                (coe v16)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> coe v13
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                          _ -> MAlonzo.RTE.mazUnreachableError))))))) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1'45''8804'_308
                                (coe v0))))
                       erased
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_poa'45'fun_54 v6
        -> let v7
                 = coe
                     MAlonzo.Code.Once.Grammar.FunDefBridge.du_complete'45'fundef_502
                     (coe v0) (coe v6) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 (coe v8))
                       erased
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.OpDeclBridge.sound-opDecl
d_sound'45'opDecl_338 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpDecl_56
d_sound'45'opDecl_338 v0 ~v1 ~v2 ~v3 ~v4
  = du_sound'45'opDecl_338 v0
du_sound'45'opDecl_338 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpDecl_56
du_sound'45'opDecl_338 v0
  = case coe v0 of
      (:) v1 v2
        -> coe
             seq (coe v1)
             (let v3
                    = MAlonzo.Code.Once.Parser.Module.OpName.d_parseOpCharsB_58
                        (coe v2) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> let v9
                                            = MAlonzo.Code.Once.Parser.Module.FunDef.OpDecl.d_toda'45'go_54
                                                (coe v5) (coe v7)
                                                (coe
                                                   MAlonzo.Code.Once.Parser.Module.DeclTail.d_colonHead_300
                                                   (coe v7)) in
                                      coe
                                        (case coe v9 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                             -> case coe v10 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                    -> coe
                                                         seq (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_pod'45'mk_68
                                                            v5 v7
                                                            (coe
                                                               du_sound'45'opChars_16 (coe v2)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                            (coe
                                                               du_sound'45'opAfter_200 (coe v5)
                                                               (coe v7)))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.OpDeclBridge.complete-opDecl
d_complete'45'opDecl_394 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpDecl_56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'opDecl_394 v0 ~v1 ~v2 v3
  = du_complete'45'opDecl_394 v0 v3
du_complete'45'opDecl_394 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpDecl_56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'opDecl_394 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Grammar.OpDecl.C_pod'45'mk_68 v3 v4 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> let v11
                        = coe du_complete'45'opChars_158 (coe v10) (coe v4) (coe v7) in
                  coe
                    (case coe v11 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                         -> let v14 = coe du_complete'45'opAfter_280 (coe v4) (coe v8) in
                            coe
                              (case coe v14 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                           (coe v15)
                                           (coe
                                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                 (coe
                                                    (\ v17 v18 ->
                                                       addInt (coe (1 :: Integer)) (coe v18)))
                                                 (coe (0 :: Integer)) (coe v10))
                                              (coe v12)
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                 (coe
                                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
                                                    (coe
                                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                                       (coe
                                                          (\ v17 v18 ->
                                                             addInt (coe (1 :: Integer)) (coe v18)))
                                                       (coe (0 :: Integer)) (coe v10))))))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
