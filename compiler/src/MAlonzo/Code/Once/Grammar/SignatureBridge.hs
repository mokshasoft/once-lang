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

module MAlonzo.Code.Once.Grammar.SignatureBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Grammar.PolyTypeBridge
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.PolyInst
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.DeclTail
import qualified MAlonzo.Code.Once.Parser.PolyType
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.SigEffect
import qualified MAlonzo.Code.Once.Spec.Grammar.Signature

-- Once.Grammar.SignatureBridge.sound-effAnnot-go
d_sound'45'effAnnot'45'go_10 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Once.SigEffect.T_SigEffect_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesEffAnnot_8
d_sound'45'effAnnot'45'go_10 ~v0 v1 ~v2
  = du_sound'45'effAnnot'45'go_10 v1
du_sound'45'effAnnot'45'go_10 ::
  Maybe MAlonzo.Code.Once.SigEffect.T_SigEffect_4 ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesEffAnnot_8
du_sound'45'effAnnot'45'go_10 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Once.Spec.Grammar.Signature.C_pea'45'some_14
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Spec.Grammar.Signature.C_pea'45'none_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.SignatureBridge.sound-effAnnot
d_sound'45'effAnnot_24 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesEffAnnot_8
d_sound'45'effAnnot_24 v0
  = coe
      du_sound'45'effAnnot'45'go_10
      (coe
         MAlonzo.Code.Once.Parser.Module.DeclTail.d_effAnnotShape_264
         (coe v0))
-- Once.Grammar.SignatureBridge.complete-effAnnot-go
d_complete'45'effAnnot'45'go_38 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Once.SigEffect.T_SigEffect_4 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Once.SigEffect.T_SigEffect_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesEffAnnot_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'effAnnot'45'go_38 v0 ~v1 ~v2 v3 ~v4 v5
  = du_complete'45'effAnnot'45'go_38 v0 v3 v5
du_complete'45'effAnnot'45'go_38 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Once.SigEffect.T_SigEffect_4 ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesEffAnnot_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'effAnnot'45'go_38 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Parser.Module.DeclTail.d_eaDrop2'45''8804'_276
                   (coe v0))
                erased)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                   (coe MAlonzo.Code.Data.List.Base.du_length_268 v0))
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.SignatureBridge.complete-effAnnot
d_complete'45'effAnnot_90 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Once.SigEffect.T_SigEffect_4 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesEffAnnot_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'effAnnot_90 v0 ~v1 ~v2 v3
  = du_complete'45'effAnnot_90 v0 v3
du_complete'45'effAnnot_90 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesEffAnnot_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'effAnnot_90 v0 v1
  = coe
      du_complete'45'effAnnot'45'go_38 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.Module.DeclTail.d_effAnnotShape_264
         (coe v0))
      (coe v1)
-- Once.Grammar.SignatureBridge.sound-signature
d_sound'45'signature_104 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesSignature_20
d_sound'45'signature_104 v0 ~v1 ~v2 ~v3 ~v4
  = du_sound'45'signature_104 v0
du_sound'45'signature_104 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesSignature_20
du_sound'45'signature_104 v0
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
                                  = MAlonzo.Code.Once.Parser.Module.DeclTail.d_colonHead_300
                                      (coe v5) in
                            coe
                              (coe
                                 seq (coe v7)
                                 (let v8
                                        = coe
                                            MAlonzo.Code.Once.Parser.PolyType.du_ppB'45'go_542
                                            (coe
                                               MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                               (coe v5))
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
                                                            = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                                      coe
                                                        (let v12
                                                               = MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                                   (coe v5) in
                                                         coe
                                                           (let v13
                                                                  = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_tvarP_46
                                                                      (coe
                                                                         MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                                         (coe v5)) in
                                                            coe
                                                              (case coe v13 of
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                   -> case coe v14 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                          -> case coe v16 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                 -> let v19
                                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                              (coe
                                                                                                 v10)
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
                                                                                                  -> let v23
                                                                                                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                                               (coe
                                                                                                                  v9)
                                                                                                               (coe
                                                                                                                  v21)
                                                                                                               (coe
                                                                                                                  v22) in
                                                                                                     coe
                                                                                                       (case coe
                                                                                                               v23 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                                                            -> case coe
                                                                                                                      v24 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                   -> coe
                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                        (coe
                                                                                                                           v8)
                                                                                                                        (coe
                                                                                                                           v25)
                                                                                                                        (coe
                                                                                                                           v26)
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                            -> coe
                                                                                                                 v23
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                           -> case coe
                                                                                                     v19 of
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                                  -> case coe
                                                                                                            v20 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                         -> coe
                                                                                                              MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                              (coe
                                                                                                                 v8)
                                                                                                              (coe
                                                                                                                 v21)
                                                                                                              (coe
                                                                                                                 v22)
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                  -> coe
                                                                                                       v19
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                   -> let v14
                                                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                                (coe v11)
                                                                                (coe v12) in
                                                                      coe
                                                                        (case coe v14 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                             -> case coe v15 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                    -> let v18
                                                                                             = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                 (coe
                                                                                                    v10)
                                                                                                 (coe
                                                                                                    v16)
                                                                                                 (coe
                                                                                                    v17) in
                                                                                       coe
                                                                                         (case coe
                                                                                                 v18 of
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                              -> case coe
                                                                                                        v19 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                     -> let v22
                                                                                                              = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                                                  (coe
                                                                                                                     v9)
                                                                                                                  (coe
                                                                                                                     v20)
                                                                                                                  (coe
                                                                                                                     v21) in
                                                                                                        coe
                                                                                                          (case coe
                                                                                                                  v22 of
                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                                                               -> case coe
                                                                                                                         v23 of
                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                                                      -> coe
                                                                                                                           MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                           (coe
                                                                                                                              v8)
                                                                                                                           (coe
                                                                                                                              v24)
                                                                                                                           (coe
                                                                                                                              v25)
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                               -> coe
                                                                                                                    v22
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                              -> case coe
                                                                                                        v18 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                                     -> case coe
                                                                                                               v19 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                            -> coe
                                                                                                                 MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                 (coe
                                                                                                                    v8)
                                                                                                                 (coe
                                                                                                                    v20)
                                                                                                                 (coe
                                                                                                                    v21)
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                     -> coe
                                                                                                          v18
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                             -> case coe v14 of
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                                    -> case coe
                                                                                              v15 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                           -> let v18
                                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                                        (coe
                                                                                                           v9)
                                                                                                        (coe
                                                                                                           v16)
                                                                                                        (coe
                                                                                                           v17) in
                                                                                              coe
                                                                                                (case coe
                                                                                                        v18 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                                     -> case coe
                                                                                                               v19 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                            -> coe
                                                                                                                 MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                                 (coe
                                                                                                                    v8)
                                                                                                                 (coe
                                                                                                                    v20)
                                                                                                                 (coe
                                                                                                                    v21)
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                     -> coe
                                                                                                          v18
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                                           -> case coe
                                                                                                     v15 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                                  -> coe
                                                                                                       MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                       (coe
                                                                                                          v8)
                                                                                                       (coe
                                                                                                          v16)
                                                                                                       (coe
                                                                                                          v17)
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                           -> coe
                                                                                                v14
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError))))))) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> coe
                                                            MAlonzo.Code.Once.Spec.Grammar.Signature.C_psig'45'mk_34
                                                            v12
                                                            (coe
                                                               MAlonzo.Code.Once.Grammar.PolyTypeBridge.du_parsePolyTypeB'45'sound_42
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                                  (coe v5)))
                                                            (d_sound'45'effAnnot_24 (coe v12))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Grammar.SignatureBridge.complete-signature
d_complete'45'signature_190 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesSignature_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'signature_190 v0 ~v1 ~v2 v3
  = du_complete'45'signature_190 v0 v3
du_complete'45'signature_190 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesSignature_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'signature_190 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Grammar.Signature.C_psig'45'mk_34 v5 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> let v13
                        = coe
                            MAlonzo.Code.Once.Grammar.PolyTypeBridge.du_ppB'45'go'45'complete_60
                            (coe
                               MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302 (coe v12))
                            (let v13
                                   = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                             coe
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
                                               = MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                   (coe v12) in
                                         coe
                                           (let v18
                                                  = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_tvarP_46
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1_302
                                                         (coe v12)) in
                                            coe
                                              (case coe v18 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                   -> case coe v19 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                          -> case coe v21 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                 -> let v24
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                              (coe v15) (coe v20)
                                                                              (coe v22) in
                                                                    coe
                                                                      (case coe v24 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                           -> case coe v25 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                  -> let v28
                                                                                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                               (coe
                                                                                                  v14)
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
                                                                                                           v13)
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
                                                                           -> case coe v24 of
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                  -> case coe v25 of
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                         -> coe
                                                                                              MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                              (coe
                                                                                                 v13)
                                                                                              (coe
                                                                                                 v26)
                                                                                              (coe
                                                                                                 v27)
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                  -> coe v24
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v19
                                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                (coe v16) (coe v17) in
                                                      coe
                                                        (case coe v19 of
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                             -> case coe v20 of
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                    -> let v23
                                                                             = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                 (coe v15) (coe v21)
                                                                                 (coe v22) in
                                                                       coe
                                                                         (case coe v23 of
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                              -> case coe v24 of
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                     -> let v27
                                                                                              = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                                  (coe
                                                                                                     v14)
                                                                                                  (coe
                                                                                                     v25)
                                                                                                  (coe
                                                                                                     v26) in
                                                                                        coe
                                                                                          (case coe
                                                                                                  v27 of
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v28
                                                                                               -> case coe
                                                                                                         v28 of
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                      -> coe
                                                                                                           MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                           (coe
                                                                                                              v13)
                                                                                                           (coe
                                                                                                              v29)
                                                                                                           (coe
                                                                                                              v30)
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                               -> coe
                                                                                                    v27
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                              -> case coe v23 of
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                                     -> case coe
                                                                                               v24 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                            -> coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                 (coe
                                                                                                    v13)
                                                                                                 (coe
                                                                                                    v25)
                                                                                                 (coe
                                                                                                    v26)
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                     -> coe v23
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                             -> case coe v19 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                    -> case coe v20 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                           -> let v23
                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                        (coe v14)
                                                                                        (coe v21)
                                                                                        (coe v22) in
                                                                              coe
                                                                                (case coe v23 of
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                                     -> case coe
                                                                                               v24 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                            -> coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                                 (coe
                                                                                                    v13)
                                                                                                 (coe
                                                                                                    v25)
                                                                                                 (coe
                                                                                                    v26)
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                     -> coe v23
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> case coe v19 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                           -> case coe v20 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                  -> coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                                       (coe v13)
                                                                                       (coe v21)
                                                                                       (coe v22)
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                           -> coe v19
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                 _ -> MAlonzo.RTE.mazUnreachableError))))))) in
                  coe
                    (case coe v13 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                         -> let v16
                                  = coe
                                      du_complete'45'effAnnot'45'go_38 (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Parser.Module.DeclTail.d_effAnnotShape_264
                                         (coe v5))
                                      (coe v10) in
                            coe
                              (case coe v16 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                           (coe
                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                              (coe
                                                 (\ v19 v20 ->
                                                    addInt (coe (1 :: Integer)) (coe v20)))
                                              (coe (0 :: Integer)) (coe v12))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                 (coe v17) (coe v14))
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Module.DeclTail.d_colDrop1'45''8804'_308
                                                 (coe v12)))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
                                                 (coe
                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                    (coe
                                                       (\ v19 v20 ->
                                                          addInt (coe (1 :: Integer)) (coe v20)))
                                                    (coe (0 :: Integer)) (coe v12)))))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
