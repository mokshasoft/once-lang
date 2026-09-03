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

module MAlonzo.Code.Once.Grammar.DeclBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Grammar.FunDefBridge
import qualified MAlonzo.Code.Once.Grammar.ImportBridge
import qualified MAlonzo.Code.Once.Grammar.OpDeclBridge
import qualified MAlonzo.Code.Once.Grammar.PolyTypeBridge
import qualified MAlonzo.Code.Once.Grammar.SignatureBridge
import qualified MAlonzo.Code.Once.Grammar.TypeAliasBridge
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.PolyInst
import qualified MAlonzo.Code.Once.Parser.Module.Alloc
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.DeclTail
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Body
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Def
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Params
import qualified MAlonzo.Code.Once.Parser.Module.Import
import qualified MAlonzo.Code.Once.Parser.PolyType
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Grammar.Decl
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Grammar.DeclBridge.sound-decl
d_sound'45'decl_14 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.Decl.T_ParsesDecl_8
d_sound'45'decl_14 v0 ~v1 ~v2 ~v3 ~v4 = du_sound'45'decl_14 v0
du_sound'45'decl_14 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.Decl.T_ParsesDecl_8
du_sound'45'decl_14 v0
  = case coe v0 of
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
                               (coe ("import" :: Data.Text.Text))) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (let v7
                                            = coe
                                                MAlonzo.Code.Once.Parser.Module.Import.du_pib'45'path_276
                                                (coe
                                                   MAlonzo.Code.Once.Parser.Module.Import.du_pmp'45'aw_32
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                                      (coe v2))) in
                                      coe
                                        (coe
                                           seq (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'import_16
                                              (coe
                                                 MAlonzo.Code.Once.Grammar.ImportBridge.du_sound'45'import_648
                                                 (coe v2)))))
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
                                                   (coe v3) (coe ("type" :: Data.Text.Text))) in
                                      coe
                                        (case coe v7 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                             -> if coe v8
                                                  then coe
                                                         seq (coe v9)
                                                         (let v10
                                                                = coe
                                                                    MAlonzo.Code.Once.Parser.Module.DeclTail.du_pta'45'aw_180
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                                                       (coe v2)) in
                                                          coe
                                                            (coe
                                                               seq (coe v10)
                                                               (coe
                                                                  MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'typealias_24
                                                                  (coe
                                                                     MAlonzo.Code.Once.Grammar.TypeAliasBridge.du_sound'45'typealias_346
                                                                     (coe v2)))))
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
                                                                          ("signature"
                                                                           ::
                                                                           Data.Text.Text))) in
                                                          coe
                                                            (case coe v10 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                                 -> if coe v11
                                                                      then coe
                                                                             seq (coe v12)
                                                                             (let v13
                                                                                    = let v13
                                                                                            = MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                                                                                (coe
                                                                                                   v2) in
                                                                                      coe
                                                                                        (case coe
                                                                                                v13 of
                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                                             -> case coe
                                                                                                       v14 of
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                                    -> case coe
                                                                                                              v16 of
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                           -> coe
                                                                                                                MAlonzo.Code.Once.Parser.Module.DeclTail.du_psig'45'colon_352
                                                                                                                (coe
                                                                                                                   v15)
                                                                                                                (coe
                                                                                                                   v17)
                                                                                                                (coe
                                                                                                                   v18)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Once.Parser.Module.DeclTail.d_colonHead_300
                                                                                                                   (coe
                                                                                                                      v17))
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                             -> coe
                                                                                                  v13
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError) in
                                                                              coe
                                                                                (coe
                                                                                   seq (coe v13)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'signature_32
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Grammar.SignatureBridge.du_sound'45'signature_104
                                                                                         (coe
                                                                                            v2)))))
                                                                      else coe
                                                                             seq (coe v12)
                                                                             (let v13
                                                                                    = MAlonzo.Code.Once.Parser.Module.DeclTail.d_colonHead_300
                                                                                        (coe v2) in
                                                                              coe
                                                                                (if coe v13
                                                                                   then let v14
                                                                                              = coe
                                                                                                  MAlonzo.Code.Once.Parser.PolyType.du_ppB'45'go_542
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                                                                     (coe
                                                                                                        v2))
                                                                                                  (let v14
                                                                                                         = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                                                                                   coe
                                                                                                     (let v15
                                                                                                            = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                                                                                      coe
                                                                                                        (let v16
                                                                                                               = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                                                                                         coe
                                                                                                           (let v17
                                                                                                                  = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                                                                                            coe
                                                                                                              (let v18
                                                                                                                     = MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                                                                                         (coe
                                                                                                                            v2) in
                                                                                                               coe
                                                                                                                 (let v19
                                                                                                                        = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_tvarP_46
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                                                                                               (coe
                                                                                                                                  v2)) in
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
                                                                                                                                       -> let v25
                                                                                                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                                    (coe
                                                                                                                                                       v16)
                                                                                                                                                    (coe
                                                                                                                                                       v21)
                                                                                                                                                    (coe
                                                                                                                                                       v23) in
                                                                                                                                          coe
                                                                                                                                            (case coe
                                                                                                                                                    v25 of
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                                                                 -> case coe
                                                                                                                                                           v26 of
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                                                        -> let v29
                                                                                                                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                                                                                                     (coe
                                                                                                                                                                        v15)
                                                                                                                                                                     (coe
                                                                                                                                                                        v27)
                                                                                                                                                                     (coe
                                                                                                                                                                        v28) in
                                                                                                                                                           coe
                                                                                                                                                             (case coe
                                                                                                                                                                     v29 of
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v30
                                                                                                                                                                  -> case coe
                                                                                                                                                                            v30 of
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                                                         -> coe
                                                                                                                                                                              MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                                              (coe
                                                                                                                                                                                 v14)
                                                                                                                                                                              (coe
                                                                                                                                                                                 v31)
                                                                                                                                                                              (coe
                                                                                                                                                                                 v32)
                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                  -> coe
                                                                                                                                                                       v29
                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                 -> case coe
                                                                                                                                                           v25 of
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                                                                        -> case coe
                                                                                                                                                                  v26 of
                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                                                               -> coe
                                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                                    (coe
                                                                                                                                                                       v14)
                                                                                                                                                                    (coe
                                                                                                                                                                       v27)
                                                                                                                                                                    (coe
                                                                                                                                                                       v28)
                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                        -> coe
                                                                                                                                                             v25
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                         -> let v20
                                                                                                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                                                                                      (coe
                                                                                                                                         v17)
                                                                                                                                      (coe
                                                                                                                                         v18) in
                                                                                                                            coe
                                                                                                                              (case coe
                                                                                                                                      v20 of
                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                                                                   -> case coe
                                                                                                                                             v21 of
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                                                          -> let v24
                                                                                                                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                                       (coe
                                                                                                                                                          v16)
                                                                                                                                                       (coe
                                                                                                                                                          v22)
                                                                                                                                                       (coe
                                                                                                                                                          v23) in
                                                                                                                                             coe
                                                                                                                                               (case coe
                                                                                                                                                       v24 of
                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                                                    -> case coe
                                                                                                                                                              v25 of
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                                           -> let v28
                                                                                                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                                                                                                        (coe
                                                                                                                                                                           v15)
                                                                                                                                                                        (coe
                                                                                                                                                                           v26)
                                                                                                                                                                        (coe
                                                                                                                                                                           v27) in
                                                                                                                                                              coe
                                                                                                                                                                (case coe
                                                                                                                                                                        v28 of
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                                                                                                                                                                     -> case coe
                                                                                                                                                                               v29 of
                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                                                            -> coe
                                                                                                                                                                                 MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v14)
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v30)
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v31)
                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                     -> coe
                                                                                                                                                                          v28
                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                    -> case coe
                                                                                                                                                              v24 of
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                                                           -> case coe
                                                                                                                                                                     v25 of
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                                                  -> coe
                                                                                                                                                                       MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                                       (coe
                                                                                                                                                                          v14)
                                                                                                                                                                       (coe
                                                                                                                                                                          v26)
                                                                                                                                                                       (coe
                                                                                                                                                                          v27)
                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                           -> coe
                                                                                                                                                                v24
                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                   -> case coe
                                                                                                                                             v20 of
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                                                                          -> case coe
                                                                                                                                                    v21 of
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                                                                 -> let v24
                                                                                                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                                                                                              (coe
                                                                                                                                                                 v15)
                                                                                                                                                              (coe
                                                                                                                                                                 v22)
                                                                                                                                                              (coe
                                                                                                                                                                 v23) in
                                                                                                                                                    coe
                                                                                                                                                      (case coe
                                                                                                                                                              v24 of
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                                                           -> case coe
                                                                                                                                                                     v25 of
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                                                  -> coe
                                                                                                                                                                       MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                                       (coe
                                                                                                                                                                          v14)
                                                                                                                                                                       (coe
                                                                                                                                                                          v26)
                                                                                                                                                                       (coe
                                                                                                                                                                          v27)
                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                           -> coe
                                                                                                                                                                v24
                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                          -> case coe
                                                                                                                                                    v20 of
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                                                                                 -> case coe
                                                                                                                                                           v21 of
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                                                                        -> coe
                                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                             (coe
                                                                                                                                                                v14)
                                                                                                                                                             (coe
                                                                                                                                                                v22)
                                                                                                                                                             (coe
                                                                                                                                                                v23)
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                 -> coe
                                                                                                                                                      v20
                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))))))) in
                                                                                        coe
                                                                                          (case coe
                                                                                                  v14 of
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                                               -> case coe
                                                                                                         v15 of
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                                      -> case coe
                                                                                                                v17 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                                             -> let v20
                                                                                                                      = MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_eqHead_10
                                                                                                                          (coe
                                                                                                                             v18) in
                                                                                                                coe
                                                                                                                  (coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v20)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'typesig_42
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Grammar.PolyTypeBridge.du_parsePolyTypeB'45'sound_42
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                                                                                              (coe
                                                                                                                                 v2)))))
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                   else (let v14
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
                                                                                                                        (coe
                                                                                                                           v2)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                                                                                           (coe
                                                                                                                              v2)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                                                                                              (coe
                                                                                                                                 v2))))))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                                                                                           (coe
                                                                                                                              v2)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                                                                                              (coe
                                                                                                                                 v2)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                                                                                                 (coe
                                                                                                                                    v2))))))))))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                                                                               (coe
                                                                                                                  v2)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                                                                                  (coe
                                                                                                                     v2)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                                                                                     (coe
                                                                                                                        v2)))))))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_pfb'45'eq_34
                                                                                                      (coe
                                                                                                         v3)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                                                                            (coe
                                                                                                               v2)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                                                                               (coe
                                                                                                                  v2)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                                                                                  (coe
                                                                                                                     v2)))))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.Module.FunDef.Params.du_pp'45'aw_58
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                                                                                     (coe
                                                                                                                        v2)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                                                                                        (coe
                                                                                                                           v2)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                                                                                           (coe
                                                                                                                              v2))))))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                                                                                        (coe
                                                                                                                           v2)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                                                                                           (coe
                                                                                                                              v2)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                                                                                              (coe
                                                                                                                                 v2)))))))))
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
                                                                                                                        (coe
                                                                                                                           v2)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                                                                                           (coe
                                                                                                                              v2)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                                                                                              (coe
                                                                                                                                 v2))))))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                                                                                           (coe
                                                                                                                              v2)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                                                                                              (coe
                                                                                                                                 v2)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                                                                                                 (coe
                                                                                                                                    v2))))))))))
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
                                                                                                                           (coe
                                                                                                                              v2)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                                                                                              (coe
                                                                                                                                 v2)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                                                                                                 (coe
                                                                                                                                    v2))))))
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70
                                                                                                                              (coe
                                                                                                                                 v2)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34
                                                                                                                                 (coe
                                                                                                                                    v2)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                                                                                                                    (coe
                                                                                                                                       v2)))))))))))) in
                                                                                         coe
                                                                                           (coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v14)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'fundef_52
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Grammar.FunDefBridge.du_sound'45'fundef_382
                                                                                                    (coe
                                                                                                       v3)
                                                                                                    (coe
                                                                                                       v2)))))))
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> coe
                    MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'opdecl_60
                    (coe
                       MAlonzo.Code.Once.Grammar.OpDeclBridge.du_sound'45'opDecl_338
                       (coe v0))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.DeclBridge.complete-decl
d_complete'45'decl_258 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.Decl.T_ParsesDecl_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'decl_258 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'import_16 v7
        -> case coe v0 of
             (:) v8 v9
               -> let v10
                        = coe
                            MAlonzo.Code.Once.Grammar.ImportBridge.du_complete'45'import_726
                            (coe v9) (coe v2) (coe v7) in
                  coe
                    (case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe MAlonzo.Code.Data.List.Base.du_length_268 v9) (coe v11)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (let v13
                                                 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                           coe (coe (\ v14 -> v13)))
                                          (coe (0 :: Integer)) (coe v9)))))
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'typealias_24 v7
        -> case coe v0 of
             (:) v8 v9
               -> let v10
                        = MAlonzo.Code.Once.Grammar.TypeAliasBridge.d_complete'45'typealias_438
                            (coe v9) (coe v1) (coe v2) (coe v7) in
                  coe
                    (case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe MAlonzo.Code.Data.List.Base.du_length_268 v9) (coe v11)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (let v13
                                                 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                           coe (coe (\ v14 -> v13)))
                                          (coe (0 :: Integer)) (coe v9)))))
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'signature_32 v7
        -> case coe v0 of
             (:) v8 v9
               -> let v10
                        = coe
                            MAlonzo.Code.Once.Grammar.SignatureBridge.du_complete'45'signature_190
                            (coe v9) (coe v7) in
                  coe
                    (case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe MAlonzo.Code.Data.List.Base.du_length_268 v9) (coe v11)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (let v13
                                                 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                           coe (coe (\ v14 -> v13)))
                                          (coe (0 :: Integer)) (coe v9)))))
                              erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'typesig_42 v12
        -> case coe v0 of
             (:) v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Parser.Token.C_TWord_8 v16
                      -> let v17
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v17 ->
                                      coe
                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                        (coe v16))
                                   (coe
                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                      (coe v16) (coe ("import" :: Data.Text.Text))) in
                         coe
                           (case coe v17 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                -> if coe v18
                                     then coe
                                            seq (coe v19)
                                            (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                     else coe
                                            seq (coe v19)
                                            (let v20
                                                   = coe
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                       erased
                                                       (\ v20 ->
                                                          coe
                                                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                            (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                          (coe v16)
                                                          (coe ("type" :: Data.Text.Text))) in
                                             coe
                                               (case coe v20 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                    -> if coe v21
                                                         then coe
                                                                seq (coe v22)
                                                                (coe
                                                                   MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                         else coe
                                                                seq (coe v22)
                                                                (let v23
                                                                       = coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                           erased
                                                                           (\ v23 ->
                                                                              coe
                                                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                (coe v16))
                                                                           (coe
                                                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                              (coe v16)
                                                                              (coe
                                                                                 ("signature"
                                                                                  ::
                                                                                  Data.Text.Text))) in
                                                                 coe
                                                                   (case coe v23 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                        -> if coe v24
                                                                             then coe
                                                                                    seq (coe v25)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                             else coe
                                                                                    seq (coe v25)
                                                                                    (let v26
                                                                                           = coe
                                                                                               MAlonzo.Code.Once.Grammar.PolyTypeBridge.du_ppB'45'go'45'complete_60
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                                                                  (coe
                                                                                                     v15))
                                                                                               (let v26
                                                                                                      = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                                                                                coe
                                                                                                  (let v27
                                                                                                         = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                                                                                   coe
                                                                                                     (let v28
                                                                                                            = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                                                                                      coe
                                                                                                        (let v29
                                                                                                               = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                                                                                         coe
                                                                                                           (let v30
                                                                                                                  = MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                                                                                      (coe
                                                                                                                         v15) in
                                                                                                            coe
                                                                                                              (let v31
                                                                                                                     = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_tvarP_46
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                                                                                            (coe
                                                                                                                               v15)) in
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
                                                                                                                                    -> let v37
                                                                                                                                             = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                                 (coe
                                                                                                                                                    v28)
                                                                                                                                                 (coe
                                                                                                                                                    v33)
                                                                                                                                                 (coe
                                                                                                                                                    v35) in
                                                                                                                                       coe
                                                                                                                                         (case coe
                                                                                                                                                 v37 of
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v38
                                                                                                                                              -> case coe
                                                                                                                                                        v38 of
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                                                                                                                     -> let v41
                                                                                                                                                              = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                                                                                                  (coe
                                                                                                                                                                     v27)
                                                                                                                                                                  (coe
                                                                                                                                                                     v39)
                                                                                                                                                                  (coe
                                                                                                                                                                     v40) in
                                                                                                                                                        coe
                                                                                                                                                          (case coe
                                                                                                                                                                  v41 of
                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v42
                                                                                                                                                               -> case coe
                                                                                                                                                                         v42 of
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v43 v44
                                                                                                                                                                      -> coe
                                                                                                                                                                           MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                                           (coe
                                                                                                                                                                              v26)
                                                                                                                                                                           (coe
                                                                                                                                                                              v43)
                                                                                                                                                                           (coe
                                                                                                                                                                              v44)
                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                               -> coe
                                                                                                                                                                    v41
                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                              -> case coe
                                                                                                                                                        v37 of
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v38
                                                                                                                                                     -> case coe
                                                                                                                                                               v38 of
                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                                                                                                                            -> coe
                                                                                                                                                                 MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                                 (coe
                                                                                                                                                                    v26)
                                                                                                                                                                 (coe
                                                                                                                                                                    v39)
                                                                                                                                                                 (coe
                                                                                                                                                                    v40)
                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                     -> coe
                                                                                                                                                          v37
                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                      -> let v32
                                                                                                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                                                                                   (coe
                                                                                                                                      v29)
                                                                                                                                   (coe
                                                                                                                                      v30) in
                                                                                                                         coe
                                                                                                                           (case coe
                                                                                                                                   v32 of
                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v33
                                                                                                                                -> case coe
                                                                                                                                          v33 of
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                                                       -> let v36
                                                                                                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                                    (coe
                                                                                                                                                       v28)
                                                                                                                                                    (coe
                                                                                                                                                       v34)
                                                                                                                                                    (coe
                                                                                                                                                       v35) in
                                                                                                                                          coe
                                                                                                                                            (case coe
                                                                                                                                                    v36 of
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v37
                                                                                                                                                 -> case coe
                                                                                                                                                           v37 of
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                                                                        -> let v40
                                                                                                                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                                                                                                     (coe
                                                                                                                                                                        v27)
                                                                                                                                                                     (coe
                                                                                                                                                                        v38)
                                                                                                                                                                     (coe
                                                                                                                                                                        v39) in
                                                                                                                                                           coe
                                                                                                                                                             (case coe
                                                                                                                                                                     v40 of
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v41
                                                                                                                                                                  -> case coe
                                                                                                                                                                            v41 of
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                                                                                                                         -> coe
                                                                                                                                                                              MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                                              (coe
                                                                                                                                                                                 v26)
                                                                                                                                                                              (coe
                                                                                                                                                                                 v42)
                                                                                                                                                                              (coe
                                                                                                                                                                                 v43)
                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                  -> coe
                                                                                                                                                                       v40
                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                 -> case coe
                                                                                                                                                           v36 of
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v37
                                                                                                                                                        -> case coe
                                                                                                                                                                  v37 of
                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                                                                               -> coe
                                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                                    (coe
                                                                                                                                                                       v26)
                                                                                                                                                                    (coe
                                                                                                                                                                       v38)
                                                                                                                                                                    (coe
                                                                                                                                                                       v39)
                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                        -> coe
                                                                                                                                                             v36
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                -> case coe
                                                                                                                                          v32 of
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v33
                                                                                                                                       -> case coe
                                                                                                                                                 v33 of
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                                                              -> let v36
                                                                                                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                                                                                           (coe
                                                                                                                                                              v27)
                                                                                                                                                           (coe
                                                                                                                                                              v34)
                                                                                                                                                           (coe
                                                                                                                                                              v35) in
                                                                                                                                                 coe
                                                                                                                                                   (case coe
                                                                                                                                                           v36 of
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v37
                                                                                                                                                        -> case coe
                                                                                                                                                                  v37 of
                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                                                                               -> coe
                                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                                    (coe
                                                                                                                                                                       v26)
                                                                                                                                                                    (coe
                                                                                                                                                                       v38)
                                                                                                                                                                    (coe
                                                                                                                                                                       v39)
                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                        -> coe
                                                                                                                                                             v36
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                       -> case coe
                                                                                                                                                 v32 of
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v33
                                                                                                                                              -> case coe
                                                                                                                                                        v33 of
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                                                                     -> coe
                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                                                          (coe
                                                                                                                                                             v26)
                                                                                                                                                          (coe
                                                                                                                                                             v34)
                                                                                                                                                          (coe
                                                                                                                                                             v35)
                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                              -> coe
                                                                                                                                                   v32
                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))))))) in
                                                                                     coe
                                                                                       (case coe
                                                                                               v26 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                            -> coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                                                                                                          (coe
                                                                                                             v27)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1'45''8804'_308
                                                                                                             (coe
                                                                                                                v15)))))
                                                                                                 erased
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'fundef_52 v12
        -> case coe v0 of
             (:) v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Parser.Token.C_TWord_8 v15
                      -> let v16
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v16 ->
                                      coe
                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                        (coe v15))
                                   (coe
                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                      (coe v15) (coe ("import" :: Data.Text.Text))) in
                         coe
                           (case coe v16 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                -> if coe v17
                                     then coe
                                            seq (coe v18)
                                            (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                     else coe
                                            seq (coe v18)
                                            (let v19
                                                   = coe
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                       erased
                                                       (\ v19 ->
                                                          coe
                                                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                            (coe v15))
                                                       (coe
                                                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                          (coe v15)
                                                          (coe ("type" :: Data.Text.Text))) in
                                             coe
                                               (case coe v19 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                    -> if coe v20
                                                         then coe
                                                                seq (coe v21)
                                                                (coe
                                                                   MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                         else coe
                                                                seq (coe v21)
                                                                (let v22
                                                                       = coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                           erased
                                                                           (\ v22 ->
                                                                              coe
                                                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                (coe v15))
                                                                           (coe
                                                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                              (coe v15)
                                                                              (coe
                                                                                 ("signature"
                                                                                  ::
                                                                                  Data.Text.Text))) in
                                                                 coe
                                                                   (case coe v22 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                        -> if coe v23
                                                                             then coe
                                                                                    seq (coe v24)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                             else coe
                                                                                    seq (coe v24)
                                                                                    (let v25
                                                                                           = coe
                                                                                               MAlonzo.Code.Once.Grammar.FunDefBridge.du_complete'45'fundef_502
                                                                                               (coe
                                                                                                  v14)
                                                                                               (coe
                                                                                                  v12) in
                                                                                     coe
                                                                                       (case coe
                                                                                               v25 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                            -> coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                       v14)
                                                                                                    (coe
                                                                                                       v26)
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                             (let v28
                                                                                                                    = \ v28 ->
                                                                                                                        addInt
                                                                                                                          (coe
                                                                                                                             (1 ::
                                                                                                                                Integer))
                                                                                                                          (coe
                                                                                                                             v28) in
                                                                                                              coe
                                                                                                                (coe
                                                                                                                   (\ v29 ->
                                                                                                                      v28)))
                                                                                                             (coe
                                                                                                                (0 ::
                                                                                                                   Integer))
                                                                                                             (coe
                                                                                                                v14)))))
                                                                                                 erased
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grammar.Decl.C_pd'45'opdecl_60 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Once.Grammar.OpDeclBridge.du_complete'45'opDecl_394
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16) (coe v9))
                    (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
