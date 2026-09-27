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
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Generic.Sound.Make._.ParsesArrowTailG
d_ParsesArrowTailG_84 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesAtomG
d_ParsesAtomG_86 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncAtomG
d_ParsesFuncAtomG_88 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncProdG
d_ParsesFuncProdG_90 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_92 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncSumG
d_ParsesFuncSumG_94 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_96 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesProdG
d_ParsesProdG_98 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesProdTailG
d_ParsesProdTailG_100 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesSumG
d_ParsesSumG_102 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesSumTailG
d_ParsesSumTailG_104 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesTypeG
d_ParsesTypeG_106 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.arrowTailP
d_arrowTailP_286 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_286 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116 (coe v0)
-- Once.Parser.Generic.Sound.Make._.atomKw
d_atomKw_288 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_288 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128 (coe v0)
-- Once.Parser.Generic.Sound.Make._.atomP
d_atomP_290 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_290 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_104 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fAtomP
d_fAtomP_292 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_292 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_118 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fProdP
d_fProdP_294 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_294 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_120 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fProdTailP
d_fProdTailP_296 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_296 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_124 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fSumP
d_fSumP_298 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_298 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_122 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fSumTailP
d_fSumTailP_300 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_300 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_126 (coe v0)
-- Once.Parser.Generic.Sound.Make._.nuEffWith
d_nuEffWith_306 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuEffWith_306 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuEffWith_142 (coe v0)
      v2
-- Once.Parser.Generic.Sound.Make._.prodP
d_prodP_312 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_312 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_106 (coe v0)
-- Once.Parser.Generic.Sound.Make._.prodTailP
d_prodTailP_314 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_314 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112 (coe v0)
-- Once.Parser.Generic.Sound.Make._.sumP
d_sumP_316 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_316 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_108 (coe v0)
-- Once.Parser.Generic.Sound.Make._.sumTailP
d_sumTailP_318 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_318 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114 (coe v0)
-- Once.Parser.Generic.Sound.Make._.typeP
d_typeP_320 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_320 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_110 (coe v0)
-- Once.Parser.Generic.Sound.Make.sound-atom
d_sound'45'atom_330 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_386
d_sound'45'atom_330 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'atom_330 v0 v1
du_sound'45'atom_330 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_386
du_sound'45'atom_330 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_484 v7
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe du_sound'45'kw_354 (coe v0) (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-nuEff
d_sound'45'nuEff_344 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_386
d_sound'45'nuEff_344 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'nuEff_344 v0 v2
du_sound'45'nuEff_344 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_386
du_sound'45'nuEff_344 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> let v5
                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_118
                            (coe v0) (coe v3) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> let v9
                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_124
                                             (coe v0) (coe v7) (coe v8) in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                          -> case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                 -> let v13
                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_126
                                                              (coe v0) (coe v11) (coe v12) in
                                                    coe
                                                      (case coe v13 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                           -> case coe v14 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                  -> case coe v16 of
                                                                       (:) v17 v18
                                                                         -> coe
                                                                              seq (coe v17)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'eff_476
                                                                                 v15
                                                                                 (coe
                                                                                    du_sound'45'fSum_462
                                                                                    (coe v0)
                                                                                    (coe v3)))
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
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'eff_476
                                                                       v11
                                                                       (coe
                                                                          du_sound'45'fSum_462
                                                                          (coe v0) (coe v3)))
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
                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_126
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
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'eff_476
                                                                       v11
                                                                       (coe
                                                                          du_sound'45'fSum_462
                                                                          (coe v0) (coe v3)))
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
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'eff_476
                                                             v7
                                                             (coe
                                                                du_sound'45'fSum_462 (coe v0)
                                                                (coe v3)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-kw
d_sound'45'kw_354 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_386
d_sound'45'kw_354 v0 v1 ~v2 ~v3 ~v4 ~v5 = du_sound'45'kw_354 v0 v1
du_sound'45'kw_354 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_386
du_sound'45'kw_354 v0 v1
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
                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'unit_412)
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
                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'void_416)
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
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'int_420)
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
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'float_424)
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
                                                                                                                  ("Buffer"
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
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'buffer_428)
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
                                                                                                                                      ("String"
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
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'string_432)
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
                                                                                                                                                          ("Eff"
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
                                                                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212
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
                                                                                                                                                                                                du_sound'45'atom_330
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   v0)
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   v3) in
                                                                                                                                                                                      coe
                                                                                                                                                                                        (let v33
                                                                                                                                                                                               = coe
                                                                                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212
                                                                                                                                                                                                   v0
                                                                                                                                                                                                   v30 in
                                                                                                                                                                                         coe
                                                                                                                                                                                           (case coe
                                                                                                                                                                                                   v33 of
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v34
                                                                                                                                                                                                -> case coe
                                                                                                                                                                                                          v34 of
                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                                                                                                                       -> case coe
                                                                                                                                                                                                                 v36 of
                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                                                                                                                                                                              -> let v39
                                                                                                                                                                                                                       = coe
                                                                                                                                                                                                                           du_sound'45'atom_330
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              v0)
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              v30) in
                                                                                                                                                                                                                 coe
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_444
                                                                                                                                                                                                                      v30
                                                                                                                                                                                                                      v28
                                                                                                                                                                                                                      v35
                                                                                                                                                                                                                      v32
                                                                                                                                                                                                                      v39)
                                                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                -> let v34
                                                                                                                                                                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                v0)
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                v30) in
                                                                                                                                                                                                   coe
                                                                                                                                                                                                     (case coe
                                                                                                                                                                                                             v34 of
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v35
                                                                                                                                                                                                          -> case coe
                                                                                                                                                                                                                    v35 of
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                                                                                                                                                 -> let v38
                                                                                                                                                                                                                          = coe
                                                                                                                                                                                                                              du_sound'45'atom_330
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v0)
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v30) in
                                                                                                                                                                                                                    coe
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_444
                                                                                                                                                                                                                         v30
                                                                                                                                                                                                                         v28
                                                                                                                                                                                                                         v36
                                                                                                                                                                                                                         v32
                                                                                                                                                                                                                         v38)
                                                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                     -> let v27
                                                                                                                                                                              = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
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
                                                                                                                                                                                                   du_sound'45'atom_330
                                                                                                                                                                                                   (coe
                                                                                                                                                                                                      v0)
                                                                                                                                                                                                   (coe
                                                                                                                                                                                                      v3) in
                                                                                                                                                                                         coe
                                                                                                                                                                                           (let v32
                                                                                                                                                                                                  = coe
                                                                                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212
                                                                                                                                                                                                      v0
                                                                                                                                                                                                      v30 in
                                                                                                                                                                                            coe
                                                                                                                                                                                              (case coe
                                                                                                                                                                                                      v32 of
                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v33
                                                                                                                                                                                                   -> case coe
                                                                                                                                                                                                             v33 of
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                                                                                                                          -> case coe
                                                                                                                                                                                                                    v35 of
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                                                                                                                                                 -> let v38
                                                                                                                                                                                                                          = coe
                                                                                                                                                                                                                              du_sound'45'atom_330
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v0)
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v30) in
                                                                                                                                                                                                                    coe
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_444
                                                                                                                                                                                                                         v30
                                                                                                                                                                                                                         v29
                                                                                                                                                                                                                         v34
                                                                                                                                                                                                                         v31
                                                                                                                                                                                                                         v38)
                                                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                   -> let v33
                                                                                                                                                                                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                   v0)
                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                   v30) in
                                                                                                                                                                                                      coe
                                                                                                                                                                                                        (case coe
                                                                                                                                                                                                                v33 of
                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v34
                                                                                                                                                                                                             -> case coe
                                                                                                                                                                                                                       v34 of
                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                                                                                                                                    -> let v37
                                                                                                                                                                                                                             = coe
                                                                                                                                                                                                                                 du_sound'45'atom_330
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    v0)
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    v30) in
                                                                                                                                                                                                                       coe
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_444
                                                                                                                                                                                                                            v30
                                                                                                                                                                                                                            v29
                                                                                                                                                                                                                            v35
                                                                                                                                                                                                                            v31
                                                                                                                                                                                                                            v37)
                                                                                                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
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
                                                                                                                                                                              ("IO"
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
                                                                                                                                                                                        = coe
                                                                                                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212
                                                                                                                                                                                            v0
                                                                                                                                                                                            v3 in
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
                                                                                                                                                                                                                    du_sound'45'atom_330
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v0)
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v3) in
                                                                                                                                                                                                          coe
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'io_452
                                                                                                                                                                                                               v31
                                                                                                                                                                                                               v35)
                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                         -> let v30
                                                                                                                                                                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         v0)
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         v3) in
                                                                                                                                                                                            coe
                                                                                                                                                                                              (case coe
                                                                                                                                                                                                      v30 of
                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v31
                                                                                                                                                                                                   -> case coe
                                                                                                                                                                                                             v31 of
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                                                                                                          -> let v34
                                                                                                                                                                                                                   = coe
                                                                                                                                                                                                                       du_sound'45'atom_330
                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                          v0)
                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                          v3) in
                                                                                                                                                                                                             coe
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'io_452
                                                                                                                                                                                                                  v32
                                                                                                                                                                                                                  v34)
                                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
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
                                                                                                                                                                                                  ("Mu"
                                                                                                                                                                                                   ::
                                                                                                                                                                                                   Data.Text.Text))) in
                                                                                                                                                                                  coe
                                                                                                                                                                                    (case coe
                                                                                                                                                                                            v29 of
                                                                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                                                                                                         -> if coe
                                                                                                                                                                                                 v30
                                                                                                                                                                                              then coe
                                                                                                                                                                                                     seq
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v31)
                                                                                                                                                                                                     (let v32
                                                                                                                                                                                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_118
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
                                                                                                                                                                                                                             = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_124
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
                                                                                                                                                                                                                                              = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_126
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
                                                                                                                                                                                                                                                                   du_sound'45'fSum_462
                                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                                      v0)
                                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                                      v3) in
                                                                                                                                                                                                                                                         coe
                                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_460
                                                                                                                                                                                                                                                              v42
                                                                                                                                                                                                                                                              v44)
                                                                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
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
                                                                                                                                                                                                                                                         du_sound'45'fSum_462
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            v0)
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            v3) in
                                                                                                                                                                                                                                               coe
                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_460
                                                                                                                                                                                                                                                    v38
                                                                                                                                                                                                                                                    v40)
                                                                                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
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
                                                                                                                                                                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_126
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
                                                                                                                                                                                                                                                         du_sound'45'fSum_462
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            v0)
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            v3) in
                                                                                                                                                                                                                                               coe
                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_460
                                                                                                                                                                                                                                                    v38
                                                                                                                                                                                                                                                    v40)
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
                                                                                                                                                                                                                                           = coe
                                                                                                                                                                                                                                               du_sound'45'fSum_462
                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                  v0)
                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                  v3) in
                                                                                                                                                                                                                                     coe
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_460
                                                                                                                                                                                                                                          v34
                                                                                                                                                                                                                                          v36)
                                                                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                              else coe
                                                                                                                                                                                                     seq
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v31)
                                                                                                                                                                                                     (let v32
                                                                                                                                                                                                            = coe
                                                                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                erased
                                                                                                                                                                                                                (\ v32 ->
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
                                                                                                                                                                                                                v32 of
                                                                                                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                                                                                                                             -> coe
                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v34)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     seq
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        v33)
                                                                                                                                                                                                                     (let v35
                                                                                                                                                                                                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_118
                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                   v0)
                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                   v3) in
                                                                                                                                                                                                                      coe
                                                                                                                                                                                                                        (case coe
                                                                                                                                                                                                                                v35 of
                                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v36
                                                                                                                                                                                                                             -> case coe
                                                                                                                                                                                                                                       v36 of
                                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                                                                                                                                                                                                    -> let v39
                                                                                                                                                                                                                                             = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_124
                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                    v0)
                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                    v37)
                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                    v38) in
                                                                                                                                                                                                                                       coe
                                                                                                                                                                                                                                         (case coe
                                                                                                                                                                                                                                                 v39 of
                                                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v40
                                                                                                                                                                                                                                              -> case coe
                                                                                                                                                                                                                                                        v40 of
                                                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                                                                                                                                                                                                                                     -> let v43
                                                                                                                                                                                                                                                              = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_126
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     v0)
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     v41)
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     v42) in
                                                                                                                                                                                                                                                        coe
                                                                                                                                                                                                                                                          (case coe
                                                                                                                                                                                                                                                                  v43 of
                                                                                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v44
                                                                                                                                                                                                                                                               -> case coe
                                                                                                                                                                                                                                                                         v44 of
                                                                                                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v45 v46
                                                                                                                                                                                                                                                                      -> let v47
                                                                                                                                                                                                                                                                               = coe
                                                                                                                                                                                                                                                                                   du_sound'45'fSum_462
                                                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                                                      v0)
                                                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                                                      v3) in
                                                                                                                                                                                                                                                                         coe
                                                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu_468
                                                                                                                                                                                                                                                                              v45
                                                                                                                                                                                                                                                                              v47)
                                                                                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                                                               -> coe
                                                                                                                                                                                                                                                                    du_sound'45'nuEff_344
                                                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                                                       v0)
                                                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                                                       MAlonzo.Code.Once.Parser.Generic.Parser.d_effHead'63'_12
                                                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                                                          v3))
                                                                                                                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                                              -> case coe
                                                                                                                                                                                                                                                        v39 of
                                                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v40
                                                                                                                                                                                                                                                     -> case coe
                                                                                                                                                                                                                                                               v40 of
                                                                                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                                                                                                                                                                                                                                            -> let v43
                                                                                                                                                                                                                                                                     = coe
                                                                                                                                                                                                                                                                         du_sound'45'fSum_462
                                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                                            v0)
                                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                                            v3) in
                                                                                                                                                                                                                                                               coe
                                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu_468
                                                                                                                                                                                                                                                                    v41
                                                                                                                                                                                                                                                                    v43)
                                                                                                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                                                     -> coe
                                                                                                                                                                                                                                                          du_sound'45'nuEff_344
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             v0)
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Parser.d_effHead'63'_12
                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                v3))
                                                                                                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                             -> case coe
                                                                                                                                                                                                                                       v35 of
                                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v36
                                                                                                                                                                                                                                    -> case coe
                                                                                                                                                                                                                                              v36 of
                                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                                                                                                                                                                                                           -> let v39
                                                                                                                                                                                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_126
                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                           v0)
                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                           v37)
                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                           v38) in
                                                                                                                                                                                                                                              coe
                                                                                                                                                                                                                                                (case coe
                                                                                                                                                                                                                                                        v39 of
                                                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v40
                                                                                                                                                                                                                                                     -> case coe
                                                                                                                                                                                                                                                               v40 of
                                                                                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                                                                                                                                                                                                                                            -> let v43
                                                                                                                                                                                                                                                                     = coe
                                                                                                                                                                                                                                                                         du_sound'45'fSum_462
                                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                                            v0)
                                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                                            v3) in
                                                                                                                                                                                                                                                               coe
                                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu_468
                                                                                                                                                                                                                                                                    v41
                                                                                                                                                                                                                                                                    v43)
                                                                                                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                                                     -> coe
                                                                                                                                                                                                                                                          du_sound'45'nuEff_344
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             v0)
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Parser.d_effHead'63'_12
                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                v3))
                                                                                                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                                    -> case coe
                                                                                                                                                                                                                                              v35 of
                                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v36
                                                                                                                                                                                                                                           -> case coe
                                                                                                                                                                                                                                                     v36 of
                                                                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                                                                                                                                                                                                                  -> let v39
                                                                                                                                                                                                                                                           = coe
                                                                                                                                                                                                                                                               du_sound'45'fSum_462
                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                  v0)
                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                  v3) in
                                                                                                                                                                                                                                                     coe
                                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu_468
                                                                                                                                                                                                                                                          v37
                                                                                                                                                                                                                                                          v39)
                                                                                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                                           -> coe
                                                                                                                                                                                                                                                du_sound'45'nuEff_344
                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                   v0)
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
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> let v4
                        = coe
                            MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0 v3 in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> let v10
                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                                    (coe v0) (coe v6) (coe v8) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14
                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
                                                                     (coe v0) (coe v12) (coe v13) in
                                                           coe
                                                             (case coe v14 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                  -> case coe v15 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                         -> let v18
                                                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
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
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                            (coe
                                                                                                               v23))
                                                                                                         (coe
                                                                                                            du_sound'45'type_408
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
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                  (coe
                                                                                                     v19))
                                                                                               (coe
                                                                                                  du_sound'45'type_408
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
                                                                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
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
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                  (coe
                                                                                                     v19))
                                                                                               (coe
                                                                                                  du_sound'45'type_408
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
                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                        (coe v15))
                                                                                     (coe
                                                                                        du_sound'45'type_408
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
                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                                      (coe v0) (coe v3) in
                            coe
                              (case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                   -> case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                          -> let v9
                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                                       (coe v0) (coe v7) (coe v8) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> case coe v10 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                           -> let v13
                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
                                                                        (coe v0) (coe v11)
                                                                        (coe v12) in
                                                              coe
                                                                (case coe v13 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                     -> case coe v14 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                            -> let v17
                                                                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
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
                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                               (coe
                                                                                                                  v22))
                                                                                                            (coe
                                                                                                               du_sound'45'type_408
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
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                     (coe
                                                                                                        v18))
                                                                                                  (coe
                                                                                                     du_sound'45'type_408
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
                                                                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
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
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                     (coe
                                                                                                        v18))
                                                                                                  (coe
                                                                                                     du_sound'45'type_408
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
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                           (coe
                                                                                              v14))
                                                                                        (coe
                                                                                           du_sound'45'type_408
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
                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
                                                              (coe v0) (coe v7) (coe v8) in
                                                    coe
                                                      (case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                           -> case coe v10 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                  -> let v13
                                                                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
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
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                     (coe
                                                                                                        v18))
                                                                                                  (coe
                                                                                                     du_sound'45'type_408
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
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                           (coe
                                                                                              v14))
                                                                                        (coe
                                                                                           du_sound'45'type_408
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
                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
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
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                           (coe
                                                                                              v14))
                                                                                        (coe
                                                                                           du_sound'45'type_408
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
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_494
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                 (coe v10))
                                                                              (coe
                                                                                 du_sound'45'type_408
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
d_sound'45'prod_364 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_388
d_sound'45'prod_364 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'prod_364 v0 v1
du_sound'45'prod_364 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_388
du_sound'45'prod_364 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8
                                  = coe
                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_484
                                      v7 in
                            coe
                              (coe
                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_506 v6 v4 v8
                                 (coe du_sound'45'prodTail_376 (coe v0) (coe v6)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                        (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7 = coe du_sound'45'kw_354 (coe v0) (coe v1) in
                               coe
                                 (coe
                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_506 v6 v5
                                    v7 (coe du_sound'45'prodTail_376 (coe v0) (coe v6)))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-prodTail
d_sound'45'prodTail_376 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_390
d_sound'45'prodTail_376 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'prodTail_376 v0 v2
du_sound'45'prodTail_376 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_390
du_sound'45'prodTail_376 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1) in
              coe
                (let v4
                       = coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0
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
                                                   du_sound'45'atom_330 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                      (coe v1)) in
                                         coe
                                           (coe
                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'star_526
                                              v8 v6 v10
                                              (coe du_sound'45'prodTail_376 (coe v0) (coe v8)))
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                                     (coe v0) (coe v3) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                         -> let v9
                                                  = coe
                                                      du_sound'45'atom_330 (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                         (coe v1)) in
                                            coe
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'star_526
                                                 v8 v7 v9
                                                 (coe du_sound'45'prodTail_376 (coe v0) (coe v8)))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'done_512)
-- Once.Parser.Generic.Sound.Make.sound-sum
d_sound'45'sum_386 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_392
d_sound'45'sum_386 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'sum_386 v0 v1
du_sound'45'sum_386 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_392
du_sound'45'sum_386 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8
                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                      (coe v0) (coe v4) (coe v6) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> let v12
                                                   = let v12
                                                           = coe
                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_484
                                                               v7 in
                                                     coe
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_506
                                                          v6 v4 v12
                                                          (coe
                                                             du_sound'45'prodTail_376 (coe v0)
                                                             (coe v6))) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_538
                                                  v11 v10 v12
                                                  (coe du_sound'45'sumTail_398 (coe v0) (coe v11)))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                        (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7
                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                         (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = let v11
                                                              = coe
                                                                  du_sound'45'kw_354 (coe v0)
                                                                  (coe v1) in
                                                        coe
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_506
                                                             v6 v5 v11
                                                             (coe
                                                                du_sound'45'prodTail_376 (coe v0)
                                                                (coe v6))) in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_538
                                                     v10 v9 v11
                                                     (coe
                                                        du_sound'45'sumTail_398 (coe v0) (coe v10)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                            -> case coe v4 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                   -> coe
                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_538 v6
                                        v5 erased (coe du_sound'45'sumTail_398 (coe v0) (coe v6))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-sumTail
d_sound'45'sumTail_398 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_394
d_sound'45'sumTail_398 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'sumTail_398 v0 v2
du_sound'45'sumTail_398 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_394
du_sound'45'sumTail_398 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1) in
              coe
                (let v4
                       = coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0
                           (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> let v10
                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                                   (coe v0) (coe v6) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14
                                                                = coe
                                                                    du_sound'45'prod_364 (coe v0)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                       (coe v1)) in
                                                          coe
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'plus_558
                                                               v13 v12 v14
                                                               (coe
                                                                  du_sound'45'sumTail_398 (coe v0)
                                                                  (coe v13)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                                     (coe v0) (coe v3) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                         -> let v9
                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                                      (coe v0) (coe v7) (coe v8) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> case coe v10 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                          -> let v13
                                                                   = coe
                                                                       du_sound'45'prod_364 (coe v0)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                          (coe v1)) in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'plus_558
                                                                  v12 v11 v13
                                                                  (coe
                                                                     du_sound'45'sumTail_398
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
                                                             du_sound'45'prod_364 (coe v0)
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                (coe v1)) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'plus_558
                                                        v8 v7 v9
                                                        (coe
                                                           du_sound'45'sumTail_398 (coe v0)
                                                           (coe v8)))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'done_544)
-- Once.Parser.Generic.Sound.Make.sound-type
d_sound'45'type_408 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_396
d_sound'45'type_408 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'type_408 v0 v1
du_sound'45'type_408 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_396
du_sound'45'type_408 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8
                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                      (coe v0) (coe v4) (coe v6) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> let v12
                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
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
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_484
                                                                                        v7 in
                                                                              coe
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_506
                                                                                   v6 v4 v16
                                                                                   (coe
                                                                                      du_sound'45'prodTail_376
                                                                                      (coe v0)
                                                                                      (coe v6))) in
                                                                      coe
                                                                        (coe
                                                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_538
                                                                           v11 v10 v16
                                                                           (coe
                                                                              du_sound'45'sumTail_398
                                                                              (coe v0)
                                                                              (coe v11))) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_570
                                                                   v15 v14 v16
                                                                   (coe
                                                                      du_sound'45'arrowTail_420
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
                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_570
                                                      v11 v10 erased
                                                      (coe
                                                         du_sound'45'arrowTail_420 (coe v0)
                                                         (coe v11))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                        (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7
                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                         (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
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
                                                                                           du_sound'45'kw_354
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v1) in
                                                                                 coe
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_506
                                                                                      v6 v5 v15
                                                                                      (coe
                                                                                         du_sound'45'prodTail_376
                                                                                         (coe v0)
                                                                                         (coe
                                                                                            v6))) in
                                                                         coe
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_538
                                                                              v10 v9 v15
                                                                              (coe
                                                                                 du_sound'45'sumTail_398
                                                                                 (coe v0)
                                                                                 (coe v10))) in
                                                                 coe
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_570
                                                                      v14 v13 v15
                                                                      (coe
                                                                         du_sound'45'arrowTail_420
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
                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_570
                                                         v10 v9 erased
                                                         (coe
                                                            du_sound'45'arrowTail_420 (coe v0)
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
                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
                                                (coe v0) (coe v5) (coe v6) in
                                      coe
                                        (case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                             -> case coe v8 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                    -> coe
                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_570
                                                         v10 v9 erased
                                                         (coe
                                                            du_sound'45'arrowTail_420 (coe v0)
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
                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_570
                                               v6 v5 erased
                                               (coe du_sound'45'arrowTail_420 (coe v0) (coe v6))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-arrowTail
d_sound'45'arrowTail_420 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_398
d_sound'45'arrowTail_420 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'arrowTail_420 v0 v2
du_sound'45'arrowTail_420 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_398
du_sound'45'arrowTail_420 v0 v1
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
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0
                           (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34 (coe v1)) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                      -> let v11
                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                                   (coe v0) (coe v7) (coe v9) in
                                         coe
                                           (case coe v11 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                -> case coe v12 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                       -> let v15
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
                                                                    (coe v0) (coe v13) (coe v14) in
                                                          coe
                                                            (case coe v15 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                 -> case coe v16 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                        -> let v19
                                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
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
                                                                                                      du_sound'45'type_408
                                                                                                      (coe
                                                                                                         v0)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                         (coe
                                                                                                            v1)) in
                                                                                            coe
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                                                                                            du_sound'45'type_408
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
                                                                           (coe v0) (coe v13)
                                                                           (coe v14) in
                                                                 coe
                                                                   (case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                               -> let v19
                                                                                        = coe
                                                                                            du_sound'45'type_408
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                                                                                  du_sound'45'type_408
                                                                                  (coe v0)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                     (coe v1)) in
                                                                        coe
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
                                                                             v13 v3 v15)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v6
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                                     (coe v0) (coe v4) in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                  -> case coe v7 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                         -> let v10
                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                                      (coe v0) (coe v8) (coe v9) in
                                            coe
                                              (case coe v10 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                   -> case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                          -> let v14
                                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
                                                                       (coe v0) (coe v12)
                                                                       (coe v13) in
                                                             coe
                                                               (case coe v14 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                    -> case coe v15 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                           -> let v18
                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
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
                                                                                                         du_sound'45'type_408
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                            (coe
                                                                                                               v1)) in
                                                                                               coe
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                                                                                               du_sound'45'type_408
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
                                                                              (coe v0) (coe v12)
                                                                              (coe v13) in
                                                                    coe
                                                                      (case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                           -> case coe v15 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                  -> let v18
                                                                                           = coe
                                                                                               du_sound'45'type_408
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                                                                                     du_sound'45'type_408
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
                                                             (coe v0) (coe v8) (coe v9) in
                                                   coe
                                                     (case coe v10 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                          -> case coe v11 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                 -> let v14
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
                                                                              (coe v0) (coe v12)
                                                                              (coe v13) in
                                                                    coe
                                                                      (case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                           -> case coe v15 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                  -> let v18
                                                                                           = coe
                                                                                               du_sound'45'type_408
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                                                                                     du_sound'45'type_408
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
                                                                    (coe v0) (coe v8) (coe v9) in
                                                          coe
                                                            (case coe v10 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                                 -> case coe v11 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                        -> let v14
                                                                                 = coe
                                                                                     du_sound'45'type_408
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                                                                           du_sound'45'type_408
                                                                           (coe v0)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                              (coe v1)) in
                                                                 coe
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_588
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
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0
                           (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> let v10
                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                                   (coe v0) (coe v6) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
                                                                    (coe v0) (coe v12) (coe v13) in
                                                          coe
                                                            (case coe v14 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                 -> case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                        -> let v18
                                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
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
                                                                                                      du_sound'45'type_408
                                                                                                      (coe
                                                                                                         v0)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                         (coe
                                                                                                            v1)) in
                                                                                            coe
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
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
                                                                                            du_sound'45'type_408
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
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
                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
                                                                           (coe v0) (coe v12)
                                                                           (coe v13) in
                                                                 coe
                                                                   (case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> let v18
                                                                                        = coe
                                                                                            du_sound'45'type_408
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
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
                                                                                  du_sound'45'type_408
                                                                                  (coe v0)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                     (coe v1)) in
                                                                        coe
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
                                                                             v12 v14)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                                     (coe v0) (coe v3) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                         -> let v9
                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_112
                                                      (coe v0) (coe v7) (coe v8) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> case coe v10 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                          -> let v13
                                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
                                                                       (coe v0) (coe v11)
                                                                       (coe v12) in
                                                             coe
                                                               (case coe v13 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                    -> case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                           -> let v17
                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
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
                                                                                                         du_sound'45'type_408
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                            (coe
                                                                                                               v1)) in
                                                                                               coe
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
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
                                                                                               du_sound'45'type_408
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
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
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
                                                                              (coe v0) (coe v11)
                                                                              (coe v12) in
                                                                    coe
                                                                      (case coe v13 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                           -> case coe v14 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                  -> let v17
                                                                                           = coe
                                                                                               du_sound'45'type_408
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
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
                                                                                     du_sound'45'type_408
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
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
                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_114
                                                             (coe v0) (coe v7) (coe v8) in
                                                   coe
                                                     (case coe v9 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                          -> case coe v10 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                 -> let v13
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
                                                                              (coe v0) (coe v11)
                                                                              (coe v12) in
                                                                    coe
                                                                      (case coe v13 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                           -> case coe v14 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                  -> let v17
                                                                                           = coe
                                                                                               du_sound'45'type_408
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
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
                                                                                     du_sound'45'type_408
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
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
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_116
                                                                    (coe v0) (coe v7) (coe v8) in
                                                          coe
                                                            (case coe v9 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                 -> case coe v10 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                        -> let v13
                                                                                 = coe
                                                                                     du_sound'45'type_408
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
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
                                                                           du_sound'45'type_408
                                                                           (coe v0)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                              (coe v1)) in
                                                                 coe
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_598
                                                                      v7 v9)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         MAlonzo.Code.Once.Parser.Generic.Relation.C_adD_20
           -> coe MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'done_576
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-fAtom
d_sound'45'fAtom_430 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_400
d_sound'45'fAtom_430 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'fAtom_430 v0 v1
du_sound'45'fAtom_430 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_400
du_sound'45'fAtom_430 v0 v1
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
                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'id_602)
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
                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212
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
                                                                                        du_sound'45'atom_330
                                                                                        (coe v0)
                                                                                        (coe v3) in
                                                                              coe
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'k_610
                                                                                   v13 v17)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                             -> let v12
                                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_128
                                                                          (coe v0) (coe v3) in
                                                                coe
                                                                  (case coe v12 of
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                       -> case coe v13 of
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                              -> let v16
                                                                                       = coe
                                                                                           du_sound'45'atom_330
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v3) in
                                                                                 coe
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'k_610
                                                                                      v14 v16)
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                           _ -> MAlonzo.RTE.mazUnreachableError)))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError))
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> let v4
                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_118
                            (coe v0) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> let v8
                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_124
                                             (coe v0) (coe v6) (coe v7) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> let v12
                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_126
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
                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_620
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                    (coe v17))
                                                                                 (coe
                                                                                    du_sound'45'fSum_462
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
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_620
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                          (coe v13))
                                                                       (coe
                                                                          du_sound'45'fSum_462
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
                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_126
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
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_620
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                          (coe v13))
                                                                       (coe
                                                                          du_sound'45'fSum_462
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
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_620
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                (coe v9))
                                                             (coe
                                                                du_sound'45'fSum_462 (coe v0)
                                                                (coe v3)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-fProd
d_sound'45'fProd_440 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_402
d_sound'45'fProd_440 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'fProd_440 v0 v1
du_sound'45'fProd_440 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_402
du_sound'45'fProd_440 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_118
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> let v6 = coe du_sound'45'fAtom_430 (coe v0) (coe v1) in
                     coe
                       (coe
                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pfp'45'mk_632 v5 v4 v6
                          (coe du_sound'45'fProdTail_452 (coe v0) (coe v5)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-fProdTail
d_sound'45'fProdTail_452 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_404
d_sound'45'fProdTail_452 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'fProdTail_452 v0 v2
du_sound'45'fProdTail_452 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_404
du_sound'45'fProdTail_452 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_118
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
                                         du_sound'45'fAtom_430 (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                            (coe v1)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pfpt'45'star_652 v6
                                    v5 v7 (coe du_sound'45'fProdTail_452 (coe v0) (coe v6)))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_pfpt'45'done_638)
-- Once.Parser.Generic.Sound.Make.sound-fSum
d_sound'45'fSum_462 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_406
d_sound'45'fSum_462 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'fSum_462 v0 v1
du_sound'45'fSum_462 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_406
du_sound'45'fSum_462 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_118
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> let v6
                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_124
                               (coe v0) (coe v4) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                   -> let v10
                                            = let v10
                                                    = coe du_sound'45'fAtom_430 (coe v0) (coe v1) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pfp'45'mk_632
                                                   v5 v4 v10
                                                   (coe
                                                      du_sound'45'fProdTail_452 (coe v0)
                                                      (coe v5))) in
                                      coe
                                        (coe
                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfs'45'mk_664
                                           v9 v8 v10
                                           (coe du_sound'45'fSumTail_474 (coe v0) (coe v9)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                         -> coe
                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pfs'45'mk_664 v5 v4
                              erased (coe du_sound'45'fSumTail_474 (coe v0) (coe v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-fSumTail
d_sound'45'fSumTail_474 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_408
d_sound'45'fSumTail_474 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'fSumTail_474 v0 v2
du_sound'45'fSumTail_474 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_408
du_sound'45'fSumTail_474 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_118
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7
                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_124
                                         (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = coe
                                                          du_sound'45'fProd_440 (coe v0)
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                             (coe v1)) in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'plus_684
                                                     v10 v9 v11
                                                     (coe
                                                        du_sound'45'fSumTail_474 (coe v0)
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
                                                du_sound'45'fProd_440 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                   (coe v1)) in
                                      coe
                                        (coe
                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'plus_684
                                           v6 v5 v7
                                           (coe du_sound'45'fSumTail_474 (coe v0) (coe v6)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'done_670)
