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

module MAlonzo.Code.Once.Grammar.TypeAliasBridge where

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
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Grammar.ParserBridge
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.DeclTail
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Spec.Grammar.TypeAlias

-- Once.Grammar.TypeAliasBridge.sound-gtaWF
d_sound'45'gtaWF_20 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAlias_10
d_sound'45'gtaWF_20 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'gtaWF_20 v0 v1 v2
du_sound'45'gtaWF_20 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAlias_10
du_sound'45'gtaWF_20 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118 (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> let v9
                                  = coe
                                      MAlonzo.Code.Once.Parser.Module.DeclTail.du_goTypeAliasWF_26
                                      (coe v0) (coe v7)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                         (coe v2)) in
                            coe
                              (case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                   -> case coe v10 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                          -> coe
                                               seq (coe v12)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'word'45'r_34
                                                  (coe
                                                     du_sound'45'gtaWF_20 (coe v0) (coe v7)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe v5) (coe v2))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v4
                    = MAlonzo.Code.Once.Parser.Module.DeclTail.d_taEqHead_8 (coe v1) in
              coe
                (coe
                   seq (coe v4)
                   (let v5
                          = coe
                              MAlonzo.Code.Once.Parser.Type.du_parseTypeAtomWF_130
                              (coe
                                 MAlonzo.Code.Once.Parser.Module.DeclTail.d_taDrop1_10 (coe v1)) in
                    coe
                      (case coe v5 of
                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                           -> case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                  -> case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                         -> let v11
                                                  = coe
                                                      MAlonzo.Code.Once.Parser.Type.du_parseTypeProdTailWF_148
                                                      (coe v7) (coe v9) in
                                            coe
                                              (case coe v11 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                   -> case coe v12 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                          -> case coe v14 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                 -> let v17
                                                                          = coe
                                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_192
                                                                              v9 v7 v10 v16 in
                                                                    coe
                                                                      (let v18
                                                                             = coe
                                                                                 MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_154
                                                                                 (coe v13)
                                                                                 (coe v15) in
                                                                       coe
                                                                         (case coe v18 of
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                              -> case coe v19 of
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                     -> case coe
                                                                                               v21 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                            -> let v24
                                                                                                     = coe
                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                                                         v15
                                                                                                         v13
                                                                                                         v17
                                                                                                         v23 in
                                                                                               coe
                                                                                                 (let v25
                                                                                                        = coe
                                                                                                            MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
                                                                                                            (coe
                                                                                                               v20)
                                                                                                            (coe
                                                                                                               v22) in
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
                                                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                                    v22
                                                                                                                                    v20
                                                                                                                                    v24
                                                                                                                                    v30 in
                                                                                                                          coe
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                               v31)
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                         -> case coe
                                                                                                                   v25 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                                -> case coe
                                                                                                                          v26 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                       -> case coe
                                                                                                                                 v28 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                                              -> coe
                                                                                                                                   MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                                   v30
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                              -> case coe v18 of
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                     -> case coe
                                                                                               v19 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                            -> case coe
                                                                                                      v21 of
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                   -> let v24
                                                                                                            = coe
                                                                                                                MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
                                                                                                                (coe
                                                                                                                   v20)
                                                                                                                (coe
                                                                                                                   v22) in
                                                                                                      coe
                                                                                                        (case coe
                                                                                                                v24 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                             -> case coe
                                                                                                                       v25 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                    -> case coe
                                                                                                                              v27 of
                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                           -> let v30
                                                                                                                                    = coe
                                                                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                                        v22
                                                                                                                                        v20
                                                                                                                                        v23
                                                                                                                                        v29 in
                                                                                                                              coe
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                                   v30)
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                             -> case coe
                                                                                                                       v24 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                    -> case coe
                                                                                                                              v25 of
                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                           -> case coe
                                                                                                                                     v27 of
                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                                  -> coe
                                                                                                                                       MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                                       v29
                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                     -> case coe
                                                                                               v18 of
                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                            -> case coe
                                                                                                      v19 of
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                   -> case coe
                                                                                                             v21 of
                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                          -> coe
                                                                                                               MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                               v23
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                          -> case coe v12 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                 -> case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                        -> let v17
                                                                                 = coe
                                                                                     MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_154
                                                                                     (coe v13)
                                                                                     (coe v15) in
                                                                           coe
                                                                             (case coe v17 of
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                  -> case coe v18 of
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                         -> case coe
                                                                                                   v20 of
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                -> let v23
                                                                                                         = coe
                                                                                                             MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                                                             v15
                                                                                                             v13
                                                                                                             v16
                                                                                                             v22 in
                                                                                                   coe
                                                                                                     (let v24
                                                                                                            = coe
                                                                                                                MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
                                                                                                                (coe
                                                                                                                   v19)
                                                                                                                (coe
                                                                                                                   v21) in
                                                                                                      coe
                                                                                                        (case coe
                                                                                                                v24 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                             -> case coe
                                                                                                                       v25 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                    -> case coe
                                                                                                                              v27 of
                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                           -> let v30
                                                                                                                                    = coe
                                                                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                                        v21
                                                                                                                                        v19
                                                                                                                                        v23
                                                                                                                                        v29 in
                                                                                                                              coe
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                                   v30)
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                             -> case coe
                                                                                                                       v24 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                    -> case coe
                                                                                                                              v25 of
                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                           -> case coe
                                                                                                                                     v27 of
                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                                  -> coe
                                                                                                                                       MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                                       v29
                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                  -> case coe v17 of
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                         -> case coe
                                                                                                   v18 of
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                -> case coe
                                                                                                          v20 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                       -> let v23
                                                                                                                = coe
                                                                                                                    MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
                                                                                                                    (coe
                                                                                                                       v19)
                                                                                                                    (coe
                                                                                                                       v21) in
                                                                                                          coe
                                                                                                            (case coe
                                                                                                                    v23 of
                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                                                                 -> case coe
                                                                                                                           v24 of
                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                        -> case coe
                                                                                                                                  v26 of
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                               -> let v29
                                                                                                                                        = coe
                                                                                                                                            MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                                            v21
                                                                                                                                            v19
                                                                                                                                            v22
                                                                                                                                            v28 in
                                                                                                                                  coe
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                                       v29)
                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                 -> case coe
                                                                                                                           v23 of
                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                                                                        -> case coe
                                                                                                                                  v24 of
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                               -> case coe
                                                                                                                                         v26 of
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                                      -> coe
                                                                                                                                           MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                                           v28
                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                         -> case coe
                                                                                                   v17 of
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                                -> case coe
                                                                                                          v18 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                       -> case coe
                                                                                                                 v20 of
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                              -> coe
                                                                                                                   MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                   v22
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          -> case coe v11 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                        -> case coe v14 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                               -> let v17
                                                                                        = coe
                                                                                            MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
                                                                                            (coe
                                                                                               v13)
                                                                                            (coe
                                                                                               v15) in
                                                                                  coe
                                                                                    (case coe v17 of
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                         -> case coe
                                                                                                   v18 of
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                -> case coe
                                                                                                          v20 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                       -> let v23
                                                                                                                = coe
                                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                    v15
                                                                                                                    v13
                                                                                                                    v16
                                                                                                                    v22 in
                                                                                                          coe
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                               v23)
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                         -> case coe
                                                                                                   v17 of
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                                -> case coe
                                                                                                          v18 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                       -> case coe
                                                                                                                 v20 of
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                              -> coe
                                                                                                                   MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                   v22
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                 -> case coe v11 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                        -> case coe v12 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                               -> case coe v14 of
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                      -> coe
                                                                                           MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                           v16
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError
                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           -> case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                         -> case coe v8 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                -> let v11
                                                         = coe
                                                             MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_154
                                                             (coe v7) (coe v9) in
                                                   coe
                                                     (case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                          -> case coe v12 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                 -> case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                        -> let v17
                                                                                 = coe
                                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_224
                                                                                     v9 v7 v10
                                                                                     v16 in
                                                                           coe
                                                                             (let v18
                                                                                    = coe
                                                                                        MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
                                                                                        (coe v13)
                                                                                        (coe v15) in
                                                                              coe
                                                                                (case coe v18 of
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                     -> case coe
                                                                                               v19 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                            -> case coe
                                                                                                      v21 of
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                   -> let v24
                                                                                                            = coe
                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                v15
                                                                                                                v13
                                                                                                                v17
                                                                                                                v23 in
                                                                                                      coe
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                           v24)
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                     -> case coe
                                                                                               v18 of
                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                            -> case coe
                                                                                                      v19 of
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                   -> case coe
                                                                                                             v21 of
                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                          -> coe
                                                                                                               MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                               v23
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          -> case coe v11 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                        -> case coe v14 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                               -> let v17
                                                                                        = coe
                                                                                            MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
                                                                                            (coe
                                                                                               v13)
                                                                                            (coe
                                                                                               v15) in
                                                                                  coe
                                                                                    (case coe v17 of
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                         -> case coe
                                                                                                   v18 of
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                -> case coe
                                                                                                          v20 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                       -> let v23
                                                                                                                = coe
                                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                                                    v15
                                                                                                                    v13
                                                                                                                    v16
                                                                                                                    v22 in
                                                                                                          coe
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                               v23)
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                         -> case coe
                                                                                                   v17 of
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                                -> case coe
                                                                                                          v18 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                       -> case coe
                                                                                                                 v20 of
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                              -> coe
                                                                                                                   MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                                                   v22
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                 -> case coe v11 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                        -> case coe v12 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                               -> case coe v14 of
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                      -> coe
                                                                                           MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                           v16
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> case coe v5 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                         -> case coe v6 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                -> case coe v8 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                       -> let v11
                                                                = coe
                                                                    MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_160
                                                                    (coe v7) (coe v9) in
                                                          coe
                                                            (case coe v11 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                        -> case coe v14 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                               -> let v17
                                                                                        = coe
                                                                                            MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_256
                                                                                            v9 v7
                                                                                            v10
                                                                                            v16 in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                       v17)
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                 -> case coe v11 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                        -> case coe v12 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                               -> case coe v14 of
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                      -> coe
                                                                                           MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                                           v16
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> case coe v5 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                                -> case coe v6 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                       -> case coe v8 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                              -> coe
                                                                   MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22
                                                                   v10
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError
                         _ -> MAlonzo.RTE.mazUnreachableError)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Grammar.TypeAliasBridge.sound-gta
d_sound'45'gta_218 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAlias_10
d_sound'45'gta_218 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'gta_218 v0 v1 v2
du_sound'45'gta_218 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAlias_10
du_sound'45'gta_218 v0 v1 v2
  = coe du_sound'45'gtaWF_20 (coe v0) (coe v1) (coe v2)
-- Once.Grammar.TypeAliasBridge.complete-gtaWF
d_complete'45'gtaWF_242 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAlias_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'gtaWF_242 ~v0 ~v1 v2 v3 v4 ~v5 v6
  = du_complete'45'gtaWF_242 v2 v3 v4 v6
du_complete'45'gtaWF_242 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAlias_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'gtaWF_242 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'eq'45'r_22 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40 v11 v12 v13
               -> let v14
                        = coe
                            MAlonzo.Code.Once.Grammar.ParserBridge.du_complete'45'typeWFraw_300
                            (coe
                               MAlonzo.Code.Once.Parser.Module.DeclTail.d_taDrop1_10 (coe v0))
                            (coe v13) (coe v2) (coe v10) in
                  coe
                    (case coe v14 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.d_ParsesType'45'shrinks_432
                                    (coe
                                       MAlonzo.Code.Once.Parser.Module.DeclTail.d_taDrop1_10
                                       (coe v0))
                                    (coe v13) (coe v2) (coe v15))
                                 (coe
                                    MAlonzo.Code.Once.Parser.Module.DeclTail.d_taDrop1'45''8804'_16
                                    (coe v0)))
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_gta'45'word'45'r_34 v9
        -> case coe v0 of
             (:) v10 v11
               -> let v12
                        = coe
                            du_complete'45'gtaWF_242 (coe v11) (coe v1) (coe v2) (coe v9) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe MAlonzo.Code.Data.List.Base.du_length_268 v11) (coe v13)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (coe (\ v15 v16 -> addInt (coe (1 :: Integer)) (coe v16)))
                                          (coe (0 :: Integer)) (coe v11)))))
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.TypeAliasBridge.complete-gta
d_complete'45'gta_332 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAlias_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'gta_332 ~v0 ~v1 v2 v3 v4 v5
  = du_complete'45'gta_332 v2 v3 v4 v5
du_complete'45'gta_332 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAlias_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'gta_332 v0 v1 v2 v3
  = coe du_complete'45'gtaWF_242 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Grammar.TypeAliasBridge.sound-typealias
d_sound'45'typealias_346 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAliasDecl_36
d_sound'45'typealias_346 v0 ~v1 ~v2 ~v3 ~v4
  = du_sound'45'typealias_346 v0
du_sound'45'typealias_346 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAliasDecl_36
du_sound'45'typealias_346 v0
  = let v1
          = MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7
                                  = coe
                                      MAlonzo.Code.Once.Parser.Module.DeclTail.du_gta'45'aw_40
                                      (coe v3) (coe v5)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                      (coe
                                         MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                         (coe v5)) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               seq (coe v10)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_pta'45'mk_46
                                                  (coe
                                                     du_sound'45'gta_218 (coe v3) (coe v5)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Grammar.TypeAliasBridge.complete-typealias
d_complete'45'typealias_438 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAliasDecl_36 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'typealias_438 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Grammar.TypeAlias.C_pta'45'mk_46 v8
        -> case coe v0 of
             (:) v9 v10
               -> let v11
                        = coe
                            du_complete'45'gtaWF_242 (coe v10) (coe v1) (coe v2) (coe v8) in
                  coe
                    (case coe v11 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe MAlonzo.Code.Data.List.Base.du_length_268 v10) (coe v12)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (coe (\ v14 v15 -> addInt (coe (1 :: Integer)) (coe v15)))
                                          (coe (0 :: Integer)) (coe v10)))))
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
