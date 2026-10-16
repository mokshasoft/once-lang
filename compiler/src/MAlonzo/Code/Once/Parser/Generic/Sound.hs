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

module MAlonzo.Code.Once.Parser.Generic.Sound where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Generic.Sound.Make._.ParsesArrowTailG
d_ParsesArrowTailG_82 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesAtomG
d_ParsesAtomG_84 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncAtomG
d_ParsesFuncAtomG_86 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncProdG
d_ParsesFuncProdG_88 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_90 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncSumG
d_ParsesFuncSumG_92 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_94 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesProdG
d_ParsesProdG_96 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesProdTailG
d_ParsesProdTailG_98 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesSumG
d_ParsesSumG_100 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesSumTailG
d_ParsesSumTailG_102 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesTypeG
d_ParsesTypeG_104 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.arrowTailP
d_arrowTailP_284 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_284 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136 (coe v0)
-- Once.Parser.Generic.Sound.Make._.atomKw
d_atomKw_286 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_286 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148 (coe v0)
-- Once.Parser.Generic.Sound.Make._.atomP
d_atomP_288 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_288 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_124 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fAtomP
d_fAtomP_290 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_290 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fProdP
d_fProdP_292 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_292 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_140 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fProdTailP
d_fProdTailP_294 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_294 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_144 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fSumP
d_fSumP_296 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_296 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_142 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fSumTailP
d_fSumTailP_298 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_298 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146 (coe v0)
-- Once.Parser.Generic.Sound.Make._.nuEffWith
d_nuEffWith_308 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuEffWith_308 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuEffWith_162 (coe v0)
-- Once.Parser.Generic.Sound.Make._.prodP
d_prodP_314 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_314 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_126 (coe v0)
-- Once.Parser.Generic.Sound.Make._.prodTailP
d_prodTailP_316 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_316 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132 (coe v0)
-- Once.Parser.Generic.Sound.Make._.sumP
d_sumP_318 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_318 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_128 (coe v0)
-- Once.Parser.Generic.Sound.Make._.sumTailP
d_sumTailP_320 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_320 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134 (coe v0)
-- Once.Parser.Generic.Sound.Make._.typeP
d_typeP_322 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_322 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_130 (coe v0)
-- Once.Parser.Generic.Sound.Make.sound-atom
d_sound'45'atom_332 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376
d_sound'45'atom_332 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'atom_332 v0 v1
du_sound'45'atom_332 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376
du_sound'45'atom_332 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_486 v7
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe du_sound'45'kw_356 (coe v0) (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-nuEff
d_sound'45'nuEff_346 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376
d_sound'45'nuEff_346 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'nuEff_346 v0 v1 v2
du_sound'45'nuEff_346 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376
du_sound'45'nuEff_346 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138
                            (coe v0) (coe v4) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> let v10
                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_144
                                             (coe v0) (coe v8) (coe v9) in
                                   coe
                                     (case coe v10 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                          -> case coe v11 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                 -> let v14
                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
                                                              (coe v0) (coe v12) (coe v13) in
                                                    coe
                                                      (case coe v14 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                           -> case coe v15 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                  -> case coe v17 of
                                                                       (:) v18 v19
                                                                         -> coe
                                                                              seq (coe v18)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'eff_470
                                                                                 v16
                                                                                 (coe
                                                                                    du_sound'45'fSum_464
                                                                                    (coe v0)
                                                                                    (coe v4)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> case coe v13 of
                                                             (:) v14 v15
                                                               -> coe
                                                                    seq (coe v14)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'eff_470
                                                                       v12
                                                                       (coe
                                                                          du_sound'45'fSum_464
                                                                          (coe v0) (coe v4)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> let v10
                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
                                                    (coe v0) (coe v8) (coe v9) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> case coe v13 of
                                                             (:) v14 v15
                                                               -> coe
                                                                    seq (coe v14)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'eff_470
                                                                       v12
                                                                       (coe
                                                                          du_sound'45'fSum_464
                                                                          (coe v0) (coe v4)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> case coe v6 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                              -> case coe v9 of
                                                   (:) v10 v11
                                                     -> coe
                                                          seq (coe v10)
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'eff_470
                                                             v8
                                                             (coe
                                                                du_sound'45'fSum_464 (coe v0)
                                                                (coe v4)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> let v3
                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_actHead'63'_34
                     (coe v1) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7
                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138
                                      (coe v0) (coe v5) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> let v11
                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_144
                                                       (coe v0) (coe v9) (coe v10) in
                                             coe
                                               (case coe v11 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                    -> case coe v12 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                           -> let v15
                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
                                                                        (coe v0) (coe v13)
                                                                        (coe v14) in
                                                              coe
                                                                (case coe v15 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                     -> case coe v16 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                            -> case coe v18 of
                                                                                 (:) v19 v20
                                                                                   -> coe
                                                                                        seq
                                                                                        (coe v19)
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'act_478
                                                                                           v17
                                                                                           (coe
                                                                                              du_sound'45'fSum_464
                                                                                              (coe
                                                                                                 v0)
                                                                                              (coe
                                                                                                 v5)))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                           -> case coe v12 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                  -> case coe v14 of
                                                                       (:) v15 v16
                                                                         -> coe
                                                                              seq (coe v15)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'act_478
                                                                                 v13
                                                                                 (coe
                                                                                    du_sound'45'fSum_464
                                                                                    (coe v0)
                                                                                    (coe v5)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> let v11
                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
                                                              (coe v0) (coe v9) (coe v10) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                           -> case coe v12 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                  -> case coe v14 of
                                                                       (:) v15 v16
                                                                         -> coe
                                                                              seq (coe v15)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'act_478
                                                                                 v13
                                                                                 (coe
                                                                                    du_sound'45'fSum_464
                                                                                    (coe v0)
                                                                                    (coe v5)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                 -> case coe v8 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                        -> case coe v10 of
                                                             (:) v11 v12
                                                               -> coe
                                                                    seq (coe v11)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'act_478
                                                                       v9
                                                                       (coe
                                                                          du_sound'45'fSum_464
                                                                          (coe v0) (coe v5)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-kw
d_sound'45'kw_356 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376
d_sound'45'kw_356 v0 v1 ~v2 ~v3 ~v4 ~v5 = du_sound'45'kw_356 v0 v1
du_sound'45'kw_356 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376
du_sound'45'kw_356 v0 v1
  = case coe v1 of
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
                               (coe ("Unit" :: Data.Text.Text))) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'unit_402)
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
                                                   (coe v4) (coe ("Void" :: Data.Text.Text))) in
                                      coe
                                        (case coe v8 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                             -> if coe v9
                                                  then coe
                                                         seq (coe v10)
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'void_406)
                                                  else coe
                                                         seq (coe v10)
                                                         (let v11
                                                                = coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                    erased
                                                                    (\ v11 ->
                                                                       coe
                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                         (coe v4))
                                                                    (coe
                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                       (coe v4)
                                                                       (coe
                                                                          ("Int"
                                                                           ::
                                                                           Data.Text.Text))) in
                                                          coe
                                                            (case coe v11 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                                 -> if coe v12
                                                                      then coe
                                                                             seq (coe v13)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'int_410)
                                                                      else coe
                                                                             seq (coe v13)
                                                                             (let v14
                                                                                    = coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                        erased
                                                                                        (\ v14 ->
                                                                                           coe
                                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                             (coe
                                                                                                v4))
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                           (coe v4)
                                                                                           (coe
                                                                                              ("Float"
                                                                                               ::
                                                                                               Data.Text.Text))) in
                                                                              coe
                                                                                (case coe v14 of
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                                     -> if coe v15
                                                                                          then coe
                                                                                                 seq
                                                                                                 (coe
                                                                                                    v16)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'float_414)
                                                                                          else coe
                                                                                                 seq
                                                                                                 (coe
                                                                                                    v16)
                                                                                                 (let v17
                                                                                                        = coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                            erased
                                                                                                            (\ v17 ->
                                                                                                               coe
                                                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                 (coe
                                                                                                                    v4))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                               (coe
                                                                                                                  v4)
                                                                                                               (coe
                                                                                                                  ("Eff"
                                                                                                                   ::
                                                                                                                   Data.Text.Text))) in
                                                                                                  coe
                                                                                                    (case coe
                                                                                                            v17 of
                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                         -> if coe
                                                                                                                 v18
                                                                                                              then coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v19)
                                                                                                                     (let v20
                                                                                                                            = coe
                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208
                                                                                                                                v0
                                                                                                                                v3 in
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
                                                                                                                                           -> let v26
                                                                                                                                                    = coe
                                                                                                                                                        du_sound'45'atom_332
                                                                                                                                                        (coe
                                                                                                                                                           v0)
                                                                                                                                                        (coe
                                                                                                                                                           v3) in
                                                                                                                                              coe
                                                                                                                                                (let v27
                                                                                                                                                       = coe
                                                                                                                                                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208
                                                                                                                                                           v0
                                                                                                                                                           v24 in
                                                                                                                                                 coe
                                                                                                                                                   (case coe
                                                                                                                                                           v27 of
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v28
                                                                                                                                                        -> case coe
                                                                                                                                                                  v28 of
                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                                                                               -> case coe
                                                                                                                                                                         v30 of
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                                                      -> let v33
                                                                                                                                                                               = coe
                                                                                                                                                                                   du_sound'45'atom_332
                                                                                                                                                                                   (coe
                                                                                                                                                                                      v0)
                                                                                                                                                                                   (coe
                                                                                                                                                                                      v24) in
                                                                                                                                                                         coe
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_426
                                                                                                                                                                              v24
                                                                                                                                                                              v22
                                                                                                                                                                              v29
                                                                                                                                                                              v26
                                                                                                                                                                              v33)
                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                        -> let v28
                                                                                                                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                                                                                                                                                     (coe
                                                                                                                                                                        v0)
                                                                                                                                                                     (coe
                                                                                                                                                                        v24) in
                                                                                                                                                           coe
                                                                                                                                                             (case coe
                                                                                                                                                                     v28 of
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                                                                                                                                                                  -> case coe
                                                                                                                                                                            v29 of
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                                                         -> let v32
                                                                                                                                                                                  = coe
                                                                                                                                                                                      du_sound'45'atom_332
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v0)
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v24) in
                                                                                                                                                                            coe
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_426
                                                                                                                                                                                 v24
                                                                                                                                                                                 v22
                                                                                                                                                                                 v30
                                                                                                                                                                                 v26
                                                                                                                                                                                 v32)
                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                             -> let v21
                                                                                                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                                                                                                                          (coe
                                                                                                                                             v0)
                                                                                                                                          (coe
                                                                                                                                             v3) in
                                                                                                                                coe
                                                                                                                                  (case coe
                                                                                                                                          v21 of
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                                                                                                                       -> case coe
                                                                                                                                                 v22 of
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                                                              -> let v25
                                                                                                                                                       = coe
                                                                                                                                                           du_sound'45'atom_332
                                                                                                                                                           (coe
                                                                                                                                                              v0)
                                                                                                                                                           (coe
                                                                                                                                                              v3) in
                                                                                                                                                 coe
                                                                                                                                                   (let v26
                                                                                                                                                          = coe
                                                                                                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208
                                                                                                                                                              v0
                                                                                                                                                              v24 in
                                                                                                                                                    coe
                                                                                                                                                      (case coe
                                                                                                                                                              v26 of
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v27
                                                                                                                                                           -> case coe
                                                                                                                                                                     v27 of
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                                                                  -> case coe
                                                                                                                                                                            v29 of
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                                                         -> let v32
                                                                                                                                                                                  = coe
                                                                                                                                                                                      du_sound'45'atom_332
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v0)
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v24) in
                                                                                                                                                                            coe
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_426
                                                                                                                                                                                 v24
                                                                                                                                                                                 v23
                                                                                                                                                                                 v28
                                                                                                                                                                                 v25
                                                                                                                                                                                 v32)
                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                           -> let v27
                                                                                                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                                                                                                                                                        (coe
                                                                                                                                                                           v0)
                                                                                                                                                                        (coe
                                                                                                                                                                           v24) in
                                                                                                                                                              coe
                                                                                                                                                                (case coe
                                                                                                                                                                        v27 of
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v28
                                                                                                                                                                     -> case coe
                                                                                                                                                                               v28 of
                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                                                                                            -> let v31
                                                                                                                                                                                     = coe
                                                                                                                                                                                         du_sound'45'atom_332
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v0)
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v24) in
                                                                                                                                                                               coe
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_426
                                                                                                                                                                                    v24
                                                                                                                                                                                    v23
                                                                                                                                                                                    v29
                                                                                                                                                                                    v25
                                                                                                                                                                                    v31)
                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                              else coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v19)
                                                                                                                     (let v20
                                                                                                                            = coe
                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                erased
                                                                                                                                (\ v20 ->
                                                                                                                                   coe
                                                                                                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                     (coe
                                                                                                                                        v4))
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                   (coe
                                                                                                                                      v4)
                                                                                                                                   (coe
                                                                                                                                      ("Act"
                                                                                                                                       ::
                                                                                                                                       Data.Text.Text))) in
                                                                                                                      coe
                                                                                                                        (case coe
                                                                                                                                v20 of
                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                                                                             -> if coe
                                                                                                                                     v21
                                                                                                                                  then coe
                                                                                                                                         seq
                                                                                                                                         (coe
                                                                                                                                            v22)
                                                                                                                                         (let v23
                                                                                                                                                = coe
                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208
                                                                                                                                                    v0
                                                                                                                                                    v3 in
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
                                                                                                                                                                            du_sound'45'atom_332
                                                                                                                                                                            (coe
                                                                                                                                                                               v0)
                                                                                                                                                                            (coe
                                                                                                                                                                               v3) in
                                                                                                                                                                  coe
                                                                                                                                                                    (let v30
                                                                                                                                                                           = coe
                                                                                                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208
                                                                                                                                                                               v0
                                                                                                                                                                               v27 in
                                                                                                                                                                     coe
                                                                                                                                                                       (case coe
                                                                                                                                                                               v30 of
                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v31
                                                                                                                                                                            -> case coe
                                                                                                                                                                                      v31 of
                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                                                                                   -> case coe
                                                                                                                                                                                             v33 of
                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                                                                                                          -> let v36
                                                                                                                                                                                                   = coe
                                                                                                                                                                                                       du_sound'45'atom_332
                                                                                                                                                                                                       (coe
                                                                                                                                                                                                          v0)
                                                                                                                                                                                                       (coe
                                                                                                                                                                                                          v27) in
                                                                                                                                                                                             coe
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'act_438
                                                                                                                                                                                                  v27
                                                                                                                                                                                                  v25
                                                                                                                                                                                                  v32
                                                                                                                                                                                                  v29
                                                                                                                                                                                                  v36)
                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                            -> let v31
                                                                                                                                                                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v0)
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v27) in
                                                                                                                                                                               coe
                                                                                                                                                                                 (case coe
                                                                                                                                                                                         v31 of
                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v32
                                                                                                                                                                                      -> case coe
                                                                                                                                                                                                v32 of
                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                                                                             -> let v35
                                                                                                                                                                                                      = coe
                                                                                                                                                                                                          du_sound'45'atom_332
                                                                                                                                                                                                          (coe
                                                                                                                                                                                                             v0)
                                                                                                                                                                                                          (coe
                                                                                                                                                                                                             v27) in
                                                                                                                                                                                                coe
                                                                                                                                                                                                  (coe
                                                                                                                                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'act_438
                                                                                                                                                                                                     v27
                                                                                                                                                                                                     v25
                                                                                                                                                                                                     v33
                                                                                                                                                                                                     v29
                                                                                                                                                                                                     v35)
                                                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                 -> let v24
                                                                                                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                                                                                                                                              (coe
                                                                                                                                                                 v0)
                                                                                                                                                              (coe
                                                                                                                                                                 v3) in
                                                                                                                                                    coe
                                                                                                                                                      (case coe
                                                                                                                                                              v24 of
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                                                           -> case coe
                                                                                                                                                                     v25 of
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                                                  -> let v28
                                                                                                                                                                           = coe
                                                                                                                                                                               du_sound'45'atom_332
                                                                                                                                                                               (coe
                                                                                                                                                                                  v0)
                                                                                                                                                                               (coe
                                                                                                                                                                                  v3) in
                                                                                                                                                                     coe
                                                                                                                                                                       (let v29
                                                                                                                                                                              = coe
                                                                                                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208
                                                                                                                                                                                  v0
                                                                                                                                                                                  v27 in
                                                                                                                                                                        coe
                                                                                                                                                                          (case coe
                                                                                                                                                                                  v29 of
                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v30
                                                                                                                                                                               -> case coe
                                                                                                                                                                                         v30 of
                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                                                                      -> case coe
                                                                                                                                                                                                v32 of
                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                                                                             -> let v35
                                                                                                                                                                                                      = coe
                                                                                                                                                                                                          du_sound'45'atom_332
                                                                                                                                                                                                          (coe
                                                                                                                                                                                                             v0)
                                                                                                                                                                                                          (coe
                                                                                                                                                                                                             v27) in
                                                                                                                                                                                                coe
                                                                                                                                                                                                  (coe
                                                                                                                                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'act_438
                                                                                                                                                                                                     v27
                                                                                                                                                                                                     v26
                                                                                                                                                                                                     v31
                                                                                                                                                                                                     v28
                                                                                                                                                                                                     v35)
                                                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                               -> let v30
                                                                                                                                                                                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                                                                                                                                                                            (coe
                                                                                                                                                                                               v0)
                                                                                                                                                                                            (coe
                                                                                                                                                                                               v27) in
                                                                                                                                                                                  coe
                                                                                                                                                                                    (case coe
                                                                                                                                                                                            v30 of
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v31
                                                                                                                                                                                         -> case coe
                                                                                                                                                                                                   v31 of
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                                                                                                -> let v34
                                                                                                                                                                                                         = coe
                                                                                                                                                                                                             du_sound'45'atom_332
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                v0)
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                v27) in
                                                                                                                                                                                                   coe
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'act_438
                                                                                                                                                                                                        v27
                                                                                                                                                                                                        v26
                                                                                                                                                                                                        v32
                                                                                                                                                                                                        v28
                                                                                                                                                                                                        v34)
                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                  else coe
                                                                                                                                         seq
                                                                                                                                         (coe
                                                                                                                                            v22)
                                                                                                                                         (let v23
                                                                                                                                                = coe
                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                    erased
                                                                                                                                                    (\ v23 ->
                                                                                                                                                       coe
                                                                                                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                         (coe
                                                                                                                                                            v4))
                                                                                                                                                    (coe
                                                                                                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                       (coe
                                                                                                                                                          v4)
                                                                                                                                                       (coe
                                                                                                                                                          ("IO"
                                                                                                                                                           ::
                                                                                                                                                           Data.Text.Text))) in
                                                                                                                                          coe
                                                                                                                                            (case coe
                                                                                                                                                    v23 of
                                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                                                                 -> if coe
                                                                                                                                                         v24
                                                                                                                                                      then coe
                                                                                                                                                             seq
                                                                                                                                                             (coe
                                                                                                                                                                v25)
                                                                                                                                                             (let v26
                                                                                                                                                                    = coe
                                                                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208
                                                                                                                                                                        v0
                                                                                                                                                                        v3 in
                                                                                                                                                              coe
                                                                                                                                                                (case coe
                                                                                                                                                                        v26 of
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v27
                                                                                                                                                                     -> case coe
                                                                                                                                                                               v27 of
                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                                                                            -> case coe
                                                                                                                                                                                      v29 of
                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                                                                   -> let v32
                                                                                                                                                                                            = coe
                                                                                                                                                                                                du_sound'45'atom_332
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   v0)
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   v3) in
                                                                                                                                                                                      coe
                                                                                                                                                                                        (coe
                                                                                                                                                                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'io_446
                                                                                                                                                                                           v28
                                                                                                                                                                                           v32)
                                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                     -> let v27
                                                                                                                                                                              = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                                                                                                                                                                  (coe
                                                                                                                                                                                     v0)
                                                                                                                                                                                  (coe
                                                                                                                                                                                     v3) in
                                                                                                                                                                        coe
                                                                                                                                                                          (case coe
                                                                                                                                                                                  v27 of
                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v28
                                                                                                                                                                               -> case coe
                                                                                                                                                                                         v28 of
                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                                                                                                      -> let v31
                                                                                                                                                                                               = coe
                                                                                                                                                                                                   du_sound'45'atom_332
                                                                                                                                                                                                   (coe
                                                                                                                                                                                                      v0)
                                                                                                                                                                                                   (coe
                                                                                                                                                                                                      v3) in
                                                                                                                                                                                         coe
                                                                                                                                                                                           (coe
                                                                                                                                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'io_446
                                                                                                                                                                                              v29
                                                                                                                                                                                              v31)
                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                      else coe
                                                                                                                                                             seq
                                                                                                                                                             (coe
                                                                                                                                                                v25)
                                                                                                                                                             (let v26
                                                                                                                                                                    = coe
                                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                        erased
                                                                                                                                                                        (\ v26 ->
                                                                                                                                                                           coe
                                                                                                                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                             (coe
                                                                                                                                                                                v4))
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                           (coe
                                                                                                                                                                              v4)
                                                                                                                                                                           (coe
                                                                                                                                                                              ("Mu"
                                                                                                                                                                               ::
                                                                                                                                                                               Data.Text.Text))) in
                                                                                                                                                              coe
                                                                                                                                                                (case coe
                                                                                                                                                                        v26 of
                                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                                                                     -> if coe
                                                                                                                                                                             v27
                                                                                                                                                                          then coe
                                                                                                                                                                                 seq
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v28)
                                                                                                                                                                                 (let v29
                                                                                                                                                                                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138
                                                                                                                                                                                            (coe
                                                                                                                                                                                               v0)
                                                                                                                                                                                            (coe
                                                                                                                                                                                               v3) in
                                                                                                                                                                                  coe
                                                                                                                                                                                    (case coe
                                                                                                                                                                                            v29 of
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v30
                                                                                                                                                                                         -> case coe
                                                                                                                                                                                                   v30 of
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                                                                                -> let v33
                                                                                                                                                                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_144
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                v0)
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                v31)
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                v32) in
                                                                                                                                                                                                   coe
                                                                                                                                                                                                     (case coe
                                                                                                                                                                                                             v33 of
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v34
                                                                                                                                                                                                          -> case coe
                                                                                                                                                                                                                    v34 of
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                                                                                                                                 -> let v37
                                                                                                                                                                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v0)
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v35)
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v36) in
                                                                                                                                                                                                                    coe
                                                                                                                                                                                                                      (case coe
                                                                                                                                                                                                                              v37 of
                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v38
                                                                                                                                                                                                                           -> case coe
                                                                                                                                                                                                                                     v38 of
                                                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                                                                                                                                                                                                  -> let v41
                                                                                                                                                                                                                                           = coe
                                                                                                                                                                                                                                               du_sound'45'fSum_464
                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                  v0)
                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                  v3) in
                                                                                                                                                                                                                                     coe
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_454
                                                                                                                                                                                                                                          v39
                                                                                                                                                                                                                                          v41)
                                                                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                          -> case coe
                                                                                                                                                                                                                    v33 of
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v34
                                                                                                                                                                                                                 -> case coe
                                                                                                                                                                                                                           v34 of
                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                                                                                                                                        -> let v37
                                                                                                                                                                                                                                 = coe
                                                                                                                                                                                                                                     du_sound'45'fSum_464
                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                        v0)
                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                        v3) in
                                                                                                                                                                                                                           coe
                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_454
                                                                                                                                                                                                                                v35
                                                                                                                                                                                                                                v37)
                                                                                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                         -> case coe
                                                                                                                                                                                                   v29 of
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v30
                                                                                                                                                                                                -> case coe
                                                                                                                                                                                                          v30 of
                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                                                                                       -> let v33
                                                                                                                                                                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v0)
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v31)
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v32) in
                                                                                                                                                                                                          coe
                                                                                                                                                                                                            (case coe
                                                                                                                                                                                                                    v33 of
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v34
                                                                                                                                                                                                                 -> case coe
                                                                                                                                                                                                                           v34 of
                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                                                                                                                                        -> let v37
                                                                                                                                                                                                                                 = coe
                                                                                                                                                                                                                                     du_sound'45'fSum_464
                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                        v0)
                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                        v3) in
                                                                                                                                                                                                                           coe
                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_454
                                                                                                                                                                                                                                v35
                                                                                                                                                                                                                                v37)
                                                                                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                -> case coe
                                                                                                                                                                                                          v29 of
                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v30
                                                                                                                                                                                                       -> case coe
                                                                                                                                                                                                                 v30 of
                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                                                                                              -> let v33
                                                                                                                                                                                                                       = coe
                                                                                                                                                                                                                           du_sound'45'fSum_464
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              v0)
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              v3) in
                                                                                                                                                                                                                 coe
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_454
                                                                                                                                                                                                                      v31
                                                                                                                                                                                                                      v33)
                                                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                          else coe
                                                                                                                                                                                 seq
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v28)
                                                                                                                                                                                 (let v29
                                                                                                                                                                                        = coe
                                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                            erased
                                                                                                                                                                                            (\ v29 ->
                                                                                                                                                                                               coe
                                                                                                                                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    v4))
                                                                                                                                                                                            (coe
                                                                                                                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  v4)
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  ("Nu"
                                                                                                                                                                                                   ::
                                                                                                                                                                                                   Data.Text.Text))) in
                                                                                                                                                                                  coe
                                                                                                                                                                                    (case coe
                                                                                                                                                                                            v29 of
                                                                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                                                                                                         -> coe
                                                                                                                                                                                              seq
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 v31)
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 seq
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    v30)
                                                                                                                                                                                                 (let v32
                                                                                                                                                                                                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               v0)
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               v3) in
                                                                                                                                                                                                  coe
                                                                                                                                                                                                    (case coe
                                                                                                                                                                                                            v32 of
                                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v33
                                                                                                                                                                                                         -> case coe
                                                                                                                                                                                                                   v33 of
                                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                                                                                                                                -> let v36
                                                                                                                                                                                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_144
                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                v0)
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
                                                                                                                                                                                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                 v0)
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
                                                                                                                                                                                                                                                  -> let v44
                                                                                                                                                                                                                                                           = coe
                                                                                                                                                                                                                                                               du_sound'45'fSum_464
                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                  v0)
                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                  v3) in
                                                                                                                                                                                                                                                     coe
                                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu_462
                                                                                                                                                                                                                                                          v42
                                                                                                                                                                                                                                                          v44)
                                                                                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                                           -> coe
                                                                                                                                                                                                                                                du_sound'45'nuEff_346
                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                   v0)
                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                   v3)
                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Parser.d_effHead'63'_12
                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                      v3))
                                                                                                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                          -> case coe
                                                                                                                                                                                                                                    v36 of
                                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v37
                                                                                                                                                                                                                                 -> case coe
                                                                                                                                                                                                                                           v37 of
                                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                                                                                                                                                        -> let v40
                                                                                                                                                                                                                                                 = coe
                                                                                                                                                                                                                                                     du_sound'45'fSum_464
                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                        v0)
                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                        v3) in
                                                                                                                                                                                                                                           coe
                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu_462
                                                                                                                                                                                                                                                v38
                                                                                                                                                                                                                                                v40)
                                                                                                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                                 -> coe
                                                                                                                                                                                                                                      du_sound'45'nuEff_346
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v0)
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v3)
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         MAlonzo.Code.Once.Parser.Generic.Parser.d_effHead'63'_12
                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                            v3))
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
                                                                                                                                                                                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                       v0)
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
                                                                                                                                                                                                                                                 = coe
                                                                                                                                                                                                                                                     du_sound'45'fSum_464
                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                        v0)
                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                        v3) in
                                                                                                                                                                                                                                           coe
                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu_462
                                                                                                                                                                                                                                                v38
                                                                                                                                                                                                                                                v40)
                                                                                                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                                 -> coe
                                                                                                                                                                                                                                      du_sound'45'nuEff_346
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v0)
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v3)
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         MAlonzo.Code.Once.Parser.Generic.Parser.d_effHead'63'_12
                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                            v3))
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
                                                                                                                                                                                                                                       = coe
                                                                                                                                                                                                                                           du_sound'45'fSum_464
                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                              v0)
                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                              v3) in
                                                                                                                                                                                                                                 coe
                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu_462
                                                                                                                                                                                                                                      v34
                                                                                                                                                                                                                                      v36)
                                                                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                       -> coe
                                                                                                                                                                                                                            du_sound'45'nuEff_346
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               v0)
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               v3)
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               MAlonzo.Code.Once.Parser.Generic.Parser.d_effHead'63'_12
                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                  v3))
                                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> let v4
                        = coe
                            MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208 v0 v3 in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> let v10
                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                                    (coe v0) (coe v6) (coe v8) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14
                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                                     (coe v0) (coe v12) (coe v13) in
                                                           coe
                                                             (case coe v14 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                  -> case coe v15 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                         -> let v18
                                                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                                      (coe v0)
                                                                                      (coe v16)
                                                                                      (coe v17) in
                                                                            coe
                                                                              (case coe v18 of
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                   -> case coe
                                                                                             v19 of
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                          -> case coe
                                                                                                    v21 of
                                                                                               (:) v22 v23
                                                                                                 -> coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v22)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                            (coe
                                                                                                               v23))
                                                                                                         (coe
                                                                                                            du_sound'45'type_410
                                                                                                            (coe
                                                                                                               v0)
                                                                                                            (coe
                                                                                                               v3)))
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> case coe v14 of
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                         -> case coe v15 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                -> case coe v17 of
                                                                                     (:) v18 v19
                                                                                       -> coe
                                                                                            seq
                                                                                            (coe
                                                                                               v18)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                  (coe
                                                                                                     v19))
                                                                                               (coe
                                                                                                  du_sound'45'type_410
                                                                                                  (coe
                                                                                                     v0)
                                                                                                  (coe
                                                                                                     v3)))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                               -> let v14
                                                                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                            (coe v0) (coe v12)
                                                                            (coe v13) in
                                                                  coe
                                                                    (case coe v14 of
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                         -> case coe v15 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                -> case coe v17 of
                                                                                     (:) v18 v19
                                                                                       -> coe
                                                                                            seq
                                                                                            (coe
                                                                                               v18)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                  (coe
                                                                                                     v19))
                                                                                               (coe
                                                                                                  du_sound'45'type_410
                                                                                                  (coe
                                                                                                     v0)
                                                                                                  (coe
                                                                                                     v3)))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                        -> case coe v10 of
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                               -> case coe v11 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                      -> case coe v13 of
                                                                           (:) v14 v15
                                                                             -> coe
                                                                                  seq (coe v14)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                        (coe v15))
                                                                                     (coe
                                                                                        du_sound'45'type_410
                                                                                        (coe v0)
                                                                                        (coe v3)))
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> let v5
                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                      (coe v0) (coe v3) in
                            coe
                              (case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                   -> case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                          -> let v9
                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                                       (coe v0) (coe v7) (coe v8) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> case coe v10 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                           -> let v13
                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                                        (coe v0) (coe v11)
                                                                        (coe v12) in
                                                              coe
                                                                (case coe v13 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                     -> case coe v14 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                            -> let v17
                                                                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                                         (coe v0)
                                                                                         (coe v15)
                                                                                         (coe
                                                                                            v16) in
                                                                               coe
                                                                                 (case coe v17 of
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                      -> case coe
                                                                                                v18 of
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                             -> case coe
                                                                                                       v20 of
                                                                                                  (:) v21 v22
                                                                                                    -> coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v21)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                               (coe
                                                                                                                  v22))
                                                                                                            (coe
                                                                                                               du_sound'45'type_410
                                                                                                               (coe
                                                                                                                  v0)
                                                                                                               (coe
                                                                                                                  v3)))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> case coe v13 of
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                            -> case coe v14 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                   -> case coe
                                                                                             v16 of
                                                                                        (:) v17 v18
                                                                                          -> coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v17)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                     (coe
                                                                                                        v18))
                                                                                                  (coe
                                                                                                     du_sound'45'type_410
                                                                                                     (coe
                                                                                                        v0)
                                                                                                     (coe
                                                                                                        v3)))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                           -> case coe v10 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                  -> let v13
                                                                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                               (coe v0) (coe v11)
                                                                               (coe v12) in
                                                                     coe
                                                                       (case coe v13 of
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                            -> case coe v14 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                   -> case coe
                                                                                             v16 of
                                                                                        (:) v17 v18
                                                                                          -> coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v17)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                     (coe
                                                                                                        v18))
                                                                                                  (coe
                                                                                                     du_sound'45'type_410
                                                                                                     (coe
                                                                                                        v0)
                                                                                                     (coe
                                                                                                        v3)))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                           -> case coe v9 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                  -> case coe v10 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                         -> case coe v12 of
                                                                              (:) v13 v14
                                                                                -> coe
                                                                                     seq (coe v13)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                           (coe
                                                                                              v14))
                                                                                        (coe
                                                                                           du_sound'45'type_410
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v3)))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> case coe v5 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                          -> case coe v6 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                 -> let v9
                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                              (coe v0) (coe v7) (coe v8) in
                                                    coe
                                                      (case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                           -> case coe v10 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                  -> let v13
                                                                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                               (coe v0) (coe v11)
                                                                               (coe v12) in
                                                                     coe
                                                                       (case coe v13 of
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                            -> case coe v14 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                   -> case coe
                                                                                             v16 of
                                                                                        (:) v17 v18
                                                                                          -> coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v17)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                     (coe
                                                                                                        v18))
                                                                                                  (coe
                                                                                                     du_sound'45'type_410
                                                                                                     (coe
                                                                                                        v0)
                                                                                                     (coe
                                                                                                        v3)))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                           -> case coe v9 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                  -> case coe v10 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                         -> case coe v12 of
                                                                              (:) v13 v14
                                                                                -> coe
                                                                                     seq (coe v13)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                           (coe
                                                                                              v14))
                                                                                        (coe
                                                                                           du_sound'45'type_410
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v3)))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> case coe v5 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                                 -> case coe v6 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                        -> let v9
                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                     (coe v0) (coe v7) (coe v8) in
                                                           coe
                                                             (case coe v9 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                  -> case coe v10 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                         -> case coe v12 of
                                                                              (:) v13 v14
                                                                                -> coe
                                                                                     seq (coe v13)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                           (coe
                                                                                              v14))
                                                                                        (coe
                                                                                           du_sound'45'type_410
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v3)))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> case coe v5 of
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                                        -> case coe v6 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                               -> case coe v8 of
                                                                    (:) v9 v10
                                                                      -> coe
                                                                           seq (coe v9)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_496
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                 (coe v10))
                                                                              (coe
                                                                                 du_sound'45'type_410
                                                                                 (coe v0) (coe v3)))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-prod
d_sound'45'prod_366 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_378
d_sound'45'prod_366 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'prod_366 v0 v1
du_sound'45'prod_366 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_378
du_sound'45'prod_366 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8
                                  = coe
                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_486
                                      v7 in
                            coe
                              (coe
                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_508 v6 v4 v8
                                 (coe du_sound'45'prodTail_378 (coe v0) (coe v6)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                        (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7 = coe du_sound'45'kw_356 (coe v0) (coe v1) in
                               coe
                                 (coe
                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_508 v6 v5
                                    v7 (coe du_sound'45'prodTail_378 (coe v0) (coe v6)))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-prodTail
d_sound'45'prodTail_378 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_380
d_sound'45'prodTail_378 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'prodTail_378 v0 v2
du_sound'45'prodTail_378 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_380
du_sound'45'prodTail_378 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1) in
              coe
                (let v4
                       = coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208 v0
                           (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> let v10
                                               = coe
                                                   du_sound'45'atom_332 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                      (coe v1)) in
                                         coe
                                           (coe
                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'star_528
                                              v8 v6 v10
                                              (coe du_sound'45'prodTail_378 (coe v0) (coe v8)))
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                     (coe v0) (coe v3) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                         -> let v9
                                                  = coe
                                                      du_sound'45'atom_332 (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                         (coe v1)) in
                                            coe
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'star_528
                                                 v8 v7 v9
                                                 (coe du_sound'45'prodTail_378 (coe v0) (coe v8)))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'done_514)
-- Once.Parser.Generic.Sound.Make.sound-sum
d_sound'45'sum_388 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_382
d_sound'45'sum_388 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'sum_388 v0 v1
du_sound'45'sum_388 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_382
du_sound'45'sum_388 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8
                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                      (coe v0) (coe v4) (coe v6) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> let v12
                                                   = let v12
                                                           = coe
                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_486
                                                               v7 in
                                                     coe
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_508
                                                          v6 v4 v12
                                                          (coe
                                                             du_sound'45'prodTail_378 (coe v0)
                                                             (coe v6))) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_540
                                                  v11 v10 v12
                                                  (coe du_sound'45'sumTail_400 (coe v0) (coe v11)))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                        (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7
                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                         (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = let v11
                                                              = coe
                                                                  du_sound'45'kw_356 (coe v0)
                                                                  (coe v1) in
                                                        coe
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_508
                                                             v6 v5 v11
                                                             (coe
                                                                du_sound'45'prodTail_378 (coe v0)
                                                                (coe v6))) in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_540
                                                     v10 v9 v11
                                                     (coe
                                                        du_sound'45'sumTail_400 (coe v0) (coe v10)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                            -> case coe v4 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                   -> coe
                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_540 v6
                                        v5 erased (coe du_sound'45'sumTail_400 (coe v0) (coe v6))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-sumTail
d_sound'45'sumTail_400 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_384
d_sound'45'sumTail_400 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'sumTail_400 v0 v2
du_sound'45'sumTail_400 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_384
du_sound'45'sumTail_400 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1) in
              coe
                (let v4
                       = coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208 v0
                           (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> let v10
                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                                   (coe v0) (coe v6) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14
                                                                = coe
                                                                    du_sound'45'prod_366 (coe v0)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                       (coe v1)) in
                                                          coe
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'plus_560
                                                               v13 v12 v14
                                                               (coe
                                                                  du_sound'45'sumTail_400 (coe v0)
                                                                  (coe v13)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                     (coe v0) (coe v3) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                         -> let v9
                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                                      (coe v0) (coe v7) (coe v8) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> case coe v10 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                          -> let v13
                                                                   = coe
                                                                       du_sound'45'prod_366 (coe v0)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                          (coe v1)) in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'plus_560
                                                                  v12 v11 v13
                                                                  (coe
                                                                     du_sound'45'sumTail_400
                                                                     (coe v0) (coe v12)))
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> case coe v5 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                         -> case coe v6 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                -> let v9
                                                         = coe
                                                             du_sound'45'prod_366 (coe v0)
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                (coe v1)) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'plus_560
                                                        v8 v7 v9
                                                        (coe
                                                           du_sound'45'sumTail_400 (coe v0)
                                                           (coe v8)))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'done_546)
-- Once.Parser.Generic.Sound.Make.sound-type
d_sound'45'type_410 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_386
d_sound'45'type_410 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'type_410 v0 v1
du_sound'45'type_410 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_386
du_sound'45'type_410 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8
                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                      (coe v0) (coe v4) (coe v6) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> let v12
                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                       (coe v0) (coe v10) (coe v11) in
                                             coe
                                               (case coe v12 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                    -> case coe v13 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                           -> let v16
                                                                    = let v16
                                                                            = let v16
                                                                                    = coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_486
                                                                                        v7 in
                                                                              coe
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_508
                                                                                   v6 v4 v16
                                                                                   (coe
                                                                                      du_sound'45'prodTail_378
                                                                                      (coe v0)
                                                                                      (coe v6))) in
                                                                      coe
                                                                        (coe
                                                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_540
                                                                           v11 v10 v16
                                                                           (coe
                                                                              du_sound'45'sumTail_400
                                                                              (coe v0)
                                                                              (coe v11))) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_572
                                                                   v15 v14 v16
                                                                   (coe
                                                                      du_sound'45'arrowTail_422
                                                                      (coe v0) (coe v15)))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> coe
                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_572
                                                      v11 v10 erased
                                                      (coe
                                                         du_sound'45'arrowTail_422 (coe v0)
                                                         (coe v11))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                        (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7
                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                         (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                          (coe v0) (coe v9) (coe v10) in
                                                coe
                                                  (case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                       -> case coe v12 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                              -> let v15
                                                                       = let v15
                                                                               = let v15
                                                                                       = coe
                                                                                           du_sound'45'kw_356
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v1) in
                                                                                 coe
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_508
                                                                                      v6 v5 v15
                                                                                      (coe
                                                                                         du_sound'45'prodTail_378
                                                                                         (coe v0)
                                                                                         (coe
                                                                                            v6))) in
                                                                         coe
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_540
                                                                              v10 v9 v15
                                                                              (coe
                                                                                 du_sound'45'sumTail_400
                                                                                 (coe v0)
                                                                                 (coe v10))) in
                                                                 coe
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_572
                                                                      v14 v13 v15
                                                                      (coe
                                                                         du_sound'45'arrowTail_422
                                                                         (coe v0) (coe v14)))
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                             -> case coe v8 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                    -> coe
                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_572
                                                         v10 v9 erased
                                                         (coe
                                                            du_sound'45'arrowTail_422 (coe v0)
                                                            (coe v10))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                            -> case coe v4 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                   -> let v7
                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                (coe v0) (coe v5) (coe v6) in
                                      coe
                                        (case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                             -> case coe v8 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                    -> coe
                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_572
                                                         v10 v9 erased
                                                         (coe
                                                            du_sound'45'arrowTail_422 (coe v0)
                                                            (coe v10))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> case coe v3 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                                   -> case coe v4 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                          -> coe
                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_572
                                               v6 v5 erased
                                               (coe du_sound'45'arrowTail_422 (coe v0) (coe v6))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-arrowTail
d_sound'45'arrowTail_422 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_388
d_sound'45'arrowTail_422 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'arrowTail_422 v0 v2
du_sound'45'arrowTail_422 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_388
du_sound'45'arrowTail_422 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_arrowDir_22
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Parser.Generic.Relation.C_adG_14 v3
           -> let v4
                    = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34 (coe v1) in
              coe
                (let v5
                       = coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208 v0
                           (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34 (coe v1)) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                      -> let v11
                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                                   (coe v0) (coe v7) (coe v9) in
                                         coe
                                           (case coe v11 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                -> case coe v12 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                       -> let v15
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                                    (coe v0) (coe v13) (coe v14) in
                                                          coe
                                                            (case coe v15 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                 -> case coe v16 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                        -> let v19
                                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                                     (coe v0)
                                                                                     (coe v17)
                                                                                     (coe v18) in
                                                                           coe
                                                                             (case coe v19 of
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                  -> case coe v20 of
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                         -> let v23
                                                                                                  = coe
                                                                                                      du_sound'45'type_410
                                                                                                      (coe
                                                                                                         v0)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                         (coe
                                                                                                            v1)) in
                                                                                            coe
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                                                 v21
                                                                                                 v3
                                                                                                 v23)
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                 -> case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                               -> let v19
                                                                                        = coe
                                                                                            du_sound'45'type_410
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                                       v17 v3 v19)
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                       -> case coe v12 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                              -> let v15
                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                           (coe v0) (coe v13)
                                                                           (coe v14) in
                                                                 coe
                                                                   (case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                               -> let v19
                                                                                        = coe
                                                                                            du_sound'45'type_410
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                                       v17 v3 v19)
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                              -> case coe v12 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                     -> let v15
                                                                              = coe
                                                                                  du_sound'45'type_410
                                                                                  (coe v0)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                     (coe v1)) in
                                                                        coe
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                             v13 v3 v15)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v6
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                     (coe v0) (coe v4) in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                  -> case coe v7 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                         -> let v10
                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                                      (coe v0) (coe v8) (coe v9) in
                                            coe
                                              (case coe v10 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                   -> case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                          -> let v14
                                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                                       (coe v0) (coe v12)
                                                                       (coe v13) in
                                                             coe
                                                               (case coe v14 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                    -> case coe v15 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                           -> let v18
                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                                        (coe v0)
                                                                                        (coe v16)
                                                                                        (coe v17) in
                                                                              coe
                                                                                (case coe v18 of
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                     -> case coe
                                                                                               v19 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                            -> let v22
                                                                                                     = coe
                                                                                                         du_sound'45'type_410
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                            (coe
                                                                                                               v1)) in
                                                                                               coe
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                                                    v20
                                                                                                    v3
                                                                                                    v22)
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                           -> case coe v15 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                  -> let v18
                                                                                           = coe
                                                                                               du_sound'45'type_410
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                                          v16 v3
                                                                                          v18)
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> case coe v10 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                          -> case coe v11 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                 -> let v14
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                              (coe v0) (coe v12)
                                                                              (coe v13) in
                                                                    coe
                                                                      (case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                           -> case coe v15 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                  -> let v18
                                                                                           = coe
                                                                                               du_sound'45'type_410
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                                          v16 v3
                                                                                          v18)
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          -> case coe v10 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                                 -> case coe v11 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                        -> let v14
                                                                                 = coe
                                                                                     du_sound'45'type_410
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                                v12 v3 v14)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                         -> case coe v7 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                -> let v10
                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                             (coe v0) (coe v8) (coe v9) in
                                                   coe
                                                     (case coe v10 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                          -> case coe v11 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                 -> let v14
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                              (coe v0) (coe v12)
                                                                              (coe v13) in
                                                                    coe
                                                                      (case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                           -> case coe v15 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                  -> let v18
                                                                                           = coe
                                                                                               du_sound'45'type_410
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                                          v16 v3
                                                                                          v18)
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          -> case coe v10 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                                 -> case coe v11 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                        -> let v14
                                                                                 = coe
                                                                                     du_sound'45'type_410
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                                v12 v3 v14)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> case coe v6 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                                -> case coe v7 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                       -> let v10
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                    (coe v0) (coe v8) (coe v9) in
                                                          coe
                                                            (case coe v10 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                                 -> case coe v11 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                        -> let v14
                                                                                 = coe
                                                                                     du_sound'45'type_410
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                                v12 v3 v14)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> case coe v6 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                                       -> case coe v7 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                              -> let v10
                                                                       = coe
                                                                           du_sound'45'type_410
                                                                           (coe v0)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                              (coe v1)) in
                                                                 coe
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_590
                                                                      v8 v3 v10)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         MAlonzo.Code.Once.Parser.Generic.Relation.C_adA_16
           -> let v3
                    = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1) in
              coe
                (let v4
                       = coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208 v0
                           (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> let v10
                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                                   (coe v0) (coe v6) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                                    (coe v0) (coe v12) (coe v13) in
                                                          coe
                                                            (case coe v14 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                 -> case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                        -> let v18
                                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                                     (coe v0)
                                                                                     (coe v16)
                                                                                     (coe v17) in
                                                                           coe
                                                                             (case coe v18 of
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                  -> case coe v19 of
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                         -> let v22
                                                                                                  = coe
                                                                                                      du_sound'45'type_410
                                                                                                      (coe
                                                                                                         v0)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                         (coe
                                                                                                            v1)) in
                                                                                            coe
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                                                 v20
                                                                                                 v22)
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                 -> case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> let v18
                                                                                        = coe
                                                                                            du_sound'45'type_410
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                                       v16 v18)
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> case coe v10 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                              -> let v14
                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                           (coe v0) (coe v12)
                                                                           (coe v13) in
                                                                 coe
                                                                   (case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> let v18
                                                                                        = coe
                                                                                            du_sound'45'type_410
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                                       v16 v18)
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                       -> case coe v10 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                              -> case coe v11 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                     -> let v14
                                                                              = coe
                                                                                  du_sound'45'type_410
                                                                                  (coe v0)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                     (coe v1)) in
                                                                        coe
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                             v12 v14)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                     (coe v0) (coe v3) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                         -> let v9
                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
                                                      (coe v0) (coe v7) (coe v8) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> case coe v10 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                          -> let v13
                                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                                       (coe v0) (coe v11)
                                                                       (coe v12) in
                                                             coe
                                                               (case coe v13 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                    -> case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                           -> let v17
                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                                        (coe v0)
                                                                                        (coe v15)
                                                                                        (coe v16) in
                                                                              coe
                                                                                (case coe v17 of
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                     -> case coe
                                                                                               v18 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                            -> let v21
                                                                                                     = coe
                                                                                                         du_sound'45'type_410
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                            (coe
                                                                                                               v1)) in
                                                                                               coe
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                                                    v19
                                                                                                    v21)
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> case coe v13 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                           -> case coe v14 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                  -> let v17
                                                                                           = coe
                                                                                               du_sound'45'type_410
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                                          v15 v17)
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> case coe v9 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                          -> case coe v10 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                 -> let v13
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                              (coe v0) (coe v11)
                                                                              (coe v12) in
                                                                    coe
                                                                      (case coe v13 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                           -> case coe v14 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                  -> let v17
                                                                                           = coe
                                                                                               du_sound'45'type_410
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                                          v15 v17)
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          -> case coe v9 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                 -> case coe v10 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                        -> let v13
                                                                                 = coe
                                                                                     du_sound'45'type_410
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                                v11 v13)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> case coe v5 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                         -> case coe v6 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                -> let v9
                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
                                                             (coe v0) (coe v7) (coe v8) in
                                                   coe
                                                     (case coe v9 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                          -> case coe v10 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                 -> let v13
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                              (coe v0) (coe v11)
                                                                              (coe v12) in
                                                                    coe
                                                                      (case coe v13 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                           -> case coe v14 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                  -> let v17
                                                                                           = coe
                                                                                               du_sound'45'type_410
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                                          v15 v17)
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          -> case coe v9 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                 -> case coe v10 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                        -> let v13
                                                                                 = coe
                                                                                     du_sound'45'type_410
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                                v11 v13)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> case coe v5 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                                -> case coe v6 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                       -> let v9
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
                                                                    (coe v0) (coe v7) (coe v8) in
                                                          coe
                                                            (case coe v9 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                 -> case coe v10 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                        -> let v13
                                                                                 = coe
                                                                                     du_sound'45'type_410
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                                v11 v13)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> case coe v5 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                                       -> case coe v6 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                              -> let v9
                                                                       = coe
                                                                           du_sound'45'type_410
                                                                           (coe v0)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                              (coe v1)) in
                                                                 coe
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_600
                                                                      v7 v9)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         MAlonzo.Code.Once.Parser.Generic.Relation.C_adD_20
           -> coe MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'done_578
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-fAtom
d_sound'45'fAtom_432 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_390
d_sound'45'fAtom_432 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'fAtom_432 v0 v1
du_sound'45'fAtom_432 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_390
du_sound'45'fAtom_432 v0 v1
  = case coe v1 of
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
                    (let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe ("K" :: Data.Text.Text))) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'id_604)
                                 else coe
                                        seq (coe v8)
                                        (case coe v6 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                             -> coe
                                                  seq (coe v10)
                                                  (coe
                                                     seq (coe v9)
                                                     (let v11
                                                            = coe
                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_208
                                                                v0 v3 in
                                                      coe
                                                        (case coe v11 of
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                             -> case coe v12 of
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                    -> case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                           -> let v17
                                                                                    = coe
                                                                                        du_sound'45'atom_332
                                                                                        (coe v0)
                                                                                        (coe v3) in
                                                                              coe
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'k_612
                                                                                   v13 v17)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                             -> let v12
                                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
                                                                          (coe v0) (coe v3) in
                                                                coe
                                                                  (case coe v12 of
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                       -> case coe v13 of
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                              -> let v16
                                                                                       = coe
                                                                                           du_sound'45'atom_332
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v3) in
                                                                                 coe
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'k_612
                                                                                      v14 v16)
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                           _ -> MAlonzo.RTE.mazUnreachableError)))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError))
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> let v4
                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138
                            (coe v0) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> let v8
                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_144
                                             (coe v0) (coe v6) (coe v7) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> let v12
                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
                                                              (coe v0) (coe v10) (coe v11) in
                                                    coe
                                                      (case coe v12 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                           -> case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                  -> case coe v15 of
                                                                       (:) v16 v17
                                                                         -> coe
                                                                              seq (coe v16)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_622
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                    (coe v17))
                                                                                 (coe
                                                                                    du_sound'45'fSum_464
                                                                                    (coe v0)
                                                                                    (coe v3)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                                 -> case coe v9 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                        -> case coe v11 of
                                                             (:) v12 v13
                                                               -> coe
                                                                    seq (coe v12)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_622
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                          (coe v13))
                                                                       (coe
                                                                          du_sound'45'fSum_464
                                                                          (coe v0) (coe v3)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> case coe v4 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                                -> case coe v5 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                       -> let v8
                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
                                                    (coe v0) (coe v6) (coe v7) in
                                          coe
                                            (case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                                 -> case coe v9 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                        -> case coe v11 of
                                                             (:) v12 v13
                                                               -> coe
                                                                    seq (coe v12)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_622
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                          (coe v13))
                                                                       (coe
                                                                          du_sound'45'fSum_464
                                                                          (coe v0) (coe v3)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> case coe v4 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                                       -> case coe v5 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                              -> case coe v7 of
                                                   (:) v8 v9
                                                     -> coe
                                                          seq (coe v8)
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_622
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                (coe v9))
                                                             (coe
                                                                du_sound'45'fSum_464 (coe v0)
                                                                (coe v3)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-fProd
d_sound'45'fProd_442 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_392
d_sound'45'fProd_442 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'fProd_442 v0 v1
du_sound'45'fProd_442 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_392
du_sound'45'fProd_442 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> let v6 = coe du_sound'45'fAtom_432 (coe v0) (coe v1) in
                     coe
                       (coe
                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pfp'45'mk_634 v5 v4 v6
                          (coe du_sound'45'fProdTail_454 (coe v0) (coe v5)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-fProdTail
d_sound'45'fProdTail_454 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_394
d_sound'45'fProdTail_454 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'fProdTail_454 v0 v2
du_sound'45'fProdTail_454 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_394
du_sound'45'fProdTail_454 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7
                                     = coe
                                         du_sound'45'fAtom_432 (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                            (coe v1)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pfpt'45'star_654 v6
                                    v5 v7 (coe du_sound'45'fProdTail_454 (coe v0) (coe v6)))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_pfpt'45'done_640)
-- Once.Parser.Generic.Sound.Make.sound-fSum
d_sound'45'fSum_464 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_396
d_sound'45'fSum_464 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'fSum_464 v0 v1
du_sound'45'fSum_464 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_396
du_sound'45'fSum_464 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> let v6
                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_144
                               (coe v0) (coe v4) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                   -> let v10
                                            = let v10
                                                    = coe du_sound'45'fAtom_432 (coe v0) (coe v1) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pfp'45'mk_634
                                                   v5 v4 v10
                                                   (coe
                                                      du_sound'45'fProdTail_454 (coe v0)
                                                      (coe v5))) in
                                      coe
                                        (coe
                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfs'45'mk_666
                                           v9 v8 v10
                                           (coe du_sound'45'fSumTail_476 (coe v0) (coe v9)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                         -> coe
                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pfs'45'mk_666 v5 v4
                              erased (coe du_sound'45'fSumTail_476 (coe v0) (coe v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-fSumTail
d_sound'45'fSumTail_476 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_398
d_sound'45'fSumTail_476 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'fSumTail_476 v0 v2
du_sound'45'fSumTail_476 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_398
du_sound'45'fSumTail_476 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7
                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_144
                                         (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = coe
                                                          du_sound'45'fProd_442 (coe v0)
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                             (coe v1)) in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'plus_686
                                                     v10 v9 v11
                                                     (coe
                                                        du_sound'45'fSumTail_476 (coe v0)
                                                        (coe v10)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                            -> case coe v4 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                   -> let v7
                                            = coe
                                                du_sound'45'fProd_442 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                   (coe v1)) in
                                      coe
                                        (coe
                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'plus_686
                                           v6 v5 v7
                                           (coe du_sound'45'fSumTail_476 (coe v0) (coe v6)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'done_672)
