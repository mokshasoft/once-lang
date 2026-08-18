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
d_ParsesArrowTailG_78 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesAtomG
d_ParsesAtomG_80 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncAtomG
d_ParsesFuncAtomG_82 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncProdG
d_ParsesFuncProdG_84 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_86 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncSumG
d_ParsesFuncSumG_88 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_90 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesProdG
d_ParsesProdG_92 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesProdTailG
d_ParsesProdTailG_94 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesSumG
d_ParsesSumG_96 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesSumTailG
d_ParsesSumTailG_98 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesTypeG
d_ParsesTypeG_100 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.arrowTailP
d_arrowTailP_272 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_272 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88 (coe v0)
-- Once.Parser.Generic.Sound.Make._.atomKw
d_atomKw_274 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_274 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100 (coe v0)
-- Once.Parser.Generic.Sound.Make._.atomP
d_atomP_276 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_276 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_76 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fAtomP
d_fAtomP_278 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_278 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_90 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fProdP
d_fProdP_280 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_280 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_92 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fProdTailP
d_fProdTailP_282 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_282 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_96 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fSumP
d_fSumP_284 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_284 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_94 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fSumTailP
d_fSumTailP_286 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_286 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_98 (coe v0)
-- Once.Parser.Generic.Sound.Make._.prodP
d_prodP_288 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_288 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_78 (coe v0)
-- Once.Parser.Generic.Sound.Make._.prodTailP
d_prodTailP_290 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_290 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84 (coe v0)
-- Once.Parser.Generic.Sound.Make._.sumP
d_sumP_292 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_292 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_80 (coe v0)
-- Once.Parser.Generic.Sound.Make._.sumTailP
d_sumTailP_294 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_294 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86 (coe v0)
-- Once.Parser.Generic.Sound.Make._.typeP
d_typeP_296 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_296 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_82 (coe v0)
-- Once.Parser.Generic.Sound.Make.sound-atom
d_sound'45'atom_306 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_364
d_sound'45'atom_306 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'atom_306 v0 v1
du_sound'45'atom_306 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_364
du_sound'45'atom_306 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_446 v7
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe du_sound'45'kw_316 (coe v0) (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-kw
d_sound'45'kw_316 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_364
d_sound'45'kw_316 v0 v1 ~v2 ~v3 ~v4 ~v5 = du_sound'45'kw_316 v0 v1
du_sound'45'kw_316 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_364
du_sound'45'kw_316 v0 v1
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
                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'unit_390)
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
                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'void_394)
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
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'int_398)
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
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'float_402)
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
                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'buffer_406)
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
                                                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'string_410)
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
                                                                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
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
                                                                                                                                                                                                du_sound'45'atom_306
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   v0)
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   v3) in
                                                                                                                                                                                      coe
                                                                                                                                                                                        (let v33
                                                                                                                                                                                               = coe
                                                                                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
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
                                                                                                                                                                                                                           du_sound'45'atom_306
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              v0)
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              v30) in
                                                                                                                                                                                                                 coe
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_422
                                                                                                                                                                                                                      v30
                                                                                                                                                                                                                      v28
                                                                                                                                                                                                                      v35
                                                                                                                                                                                                                      v32
                                                                                                                                                                                                                      v39)
                                                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                -> let v34
                                                                                                                                                                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
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
                                                                                                                                                                                                                              du_sound'45'atom_306
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v0)
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v30) in
                                                                                                                                                                                                                    coe
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_422
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
                                                                                                                                                                              = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
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
                                                                                                                                                                                                   du_sound'45'atom_306
                                                                                                                                                                                                   (coe
                                                                                                                                                                                                      v0)
                                                                                                                                                                                                   (coe
                                                                                                                                                                                                      v3) in
                                                                                                                                                                                         coe
                                                                                                                                                                                           (let v32
                                                                                                                                                                                                  = coe
                                                                                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
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
                                                                                                                                                                                                                              du_sound'45'atom_306
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v0)
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 v30) in
                                                                                                                                                                                                                    coe
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_422
                                                                                                                                                                                                                         v30
                                                                                                                                                                                                                         v29
                                                                                                                                                                                                                         v34
                                                                                                                                                                                                                         v31
                                                                                                                                                                                                                         v38)
                                                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                   -> let v33
                                                                                                                                                                                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
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
                                                                                                                                                                                                                                 du_sound'45'atom_306
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    v0)
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    v30) in
                                                                                                                                                                                                                       coe
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_422
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
                                                                                                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
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
                                                                                                                                                                                                                    du_sound'45'atom_306
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v0)
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v3) in
                                                                                                                                                                                                          coe
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'io_430
                                                                                                                                                                                                               v31
                                                                                                                                                                                                               v35)
                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                         -> let v30
                                                                                                                                                                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
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
                                                                                                                                                                                                                       du_sound'45'atom_306
                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                          v0)
                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                          v3) in
                                                                                                                                                                                                             coe
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'io_430
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
                                                                                                                                                                                         -> coe
                                                                                                                                                                                              seq
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 v31)
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 seq
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    v30)
                                                                                                                                                                                                 (let v32
                                                                                                                                                                                                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_90
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
                                                                                                                                                                                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_96
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
                                                                                                                                                                                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_98
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
                                                                                                                                                                                                                                                               du_sound'45'fSum_424
                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                  v0)
                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                  v3) in
                                                                                                                                                                                                                                                     coe
                                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_438
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
                                                                                                                                                                                                                                                     du_sound'45'fSum_424
                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                        v0)
                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                        v3) in
                                                                                                                                                                                                                                           coe
                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_438
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
                                                                                                                                                                                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_98
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
                                                                                                                                                                                                                                                     du_sound'45'fSum_424
                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                        v0)
                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                        v3) in
                                                                                                                                                                                                                                           coe
                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_438
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
                                                                                                                                                                                                                                           du_sound'45'fSum_424
                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                              v0)
                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                              v3) in
                                                                                                                                                                                                                                 coe
                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_438
                                                                                                                                                                                                                                      v34
                                                                                                                                                                                                                                      v36)
                                                                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
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
                            MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0 v3 in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> let v10
                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                    (coe v0) (coe v6) (coe v8) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14
                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                     (coe v0) (coe v12) (coe v13) in
                                                           coe
                                                             (case coe v14 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                  -> case coe v15 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                         -> let v18
                                                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
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
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                            (coe
                                                                                                               v23))
                                                                                                         (coe
                                                                                                            du_sound'45'type_370
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
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                  (coe
                                                                                                     v19))
                                                                                               (coe
                                                                                                  du_sound'45'type_370
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
                                                                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
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
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                  (coe
                                                                                                     v19))
                                                                                               (coe
                                                                                                  du_sound'45'type_370
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
                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                        (coe v15))
                                                                                     (coe
                                                                                        du_sound'45'type_370
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
                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                      (coe v0) (coe v3) in
                            coe
                              (case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                   -> case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                          -> let v9
                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                       (coe v0) (coe v7) (coe v8) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> case coe v10 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                           -> let v13
                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                        (coe v0) (coe v11)
                                                                        (coe v12) in
                                                              coe
                                                                (case coe v13 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                     -> case coe v14 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                            -> let v17
                                                                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
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
                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                               (coe
                                                                                                                  v22))
                                                                                                            (coe
                                                                                                               du_sound'45'type_370
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
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                     (coe
                                                                                                        v18))
                                                                                                  (coe
                                                                                                     du_sound'45'type_370
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
                                                                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
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
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                     (coe
                                                                                                        v18))
                                                                                                  (coe
                                                                                                     du_sound'45'type_370
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
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                           (coe
                                                                                              v14))
                                                                                        (coe
                                                                                           du_sound'45'type_370
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
                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                              (coe v0) (coe v7) (coe v8) in
                                                    coe
                                                      (case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                           -> case coe v10 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                  -> let v13
                                                                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
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
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                                     (coe
                                                                                                        v18))
                                                                                                  (coe
                                                                                                     du_sound'45'type_370
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
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                           (coe
                                                                                              v14))
                                                                                        (coe
                                                                                           du_sound'45'type_370
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
                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
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
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                           (coe
                                                                                              v14))
                                                                                        (coe
                                                                                           du_sound'45'type_370
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
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_456
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                 (coe v10))
                                                                              (coe
                                                                                 du_sound'45'type_370
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
d_sound'45'prod_326 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_366
d_sound'45'prod_326 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'prod_326 v0 v1
du_sound'45'prod_326 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_366
du_sound'45'prod_326 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8
                                  = coe
                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_446
                                      v7 in
                            coe
                              (coe
                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468 v6 v4 v8
                                 (coe du_sound'45'prodTail_338 (coe v0) (coe v6)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                        (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7 = coe du_sound'45'kw_316 (coe v0) (coe v1) in
                               coe
                                 (coe
                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468 v6 v5
                                    v7 (coe du_sound'45'prodTail_338 (coe v0) (coe v6)))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-prodTail
d_sound'45'prodTail_338 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_368
d_sound'45'prodTail_338 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'prodTail_338 v0 v2
du_sound'45'prodTail_338 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_368
du_sound'45'prodTail_338 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1) in
              coe
                (let v4
                       = coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0
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
                                                   du_sound'45'atom_306 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                      (coe v1)) in
                                         coe
                                           (coe
                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'star_488
                                              v8 v6 v10
                                              (coe du_sound'45'prodTail_338 (coe v0) (coe v8)))
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                     (coe v0) (coe v3) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                         -> let v9
                                                  = coe
                                                      du_sound'45'atom_306 (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                         (coe v1)) in
                                            coe
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'star_488
                                                 v8 v7 v9
                                                 (coe du_sound'45'prodTail_338 (coe v0) (coe v8)))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'done_474)
-- Once.Parser.Generic.Sound.Make.sound-sum
d_sound'45'sum_348 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_370
d_sound'45'sum_348 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'sum_348 v0 v1
du_sound'45'sum_348 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_370
du_sound'45'sum_348 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8
                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                      (coe v0) (coe v4) (coe v6) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> let v12
                                                   = let v12
                                                           = coe
                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_446
                                                               v7 in
                                                     coe
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                          v6 v4 v12
                                                          (coe
                                                             du_sound'45'prodTail_338 (coe v0)
                                                             (coe v6))) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                  v11 v10 v12
                                                  (coe du_sound'45'sumTail_360 (coe v0) (coe v11)))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                        (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7
                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                         (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = let v11
                                                              = coe
                                                                  du_sound'45'kw_316 (coe v0)
                                                                  (coe v1) in
                                                        coe
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                             v6 v5 v11
                                                             (coe
                                                                du_sound'45'prodTail_338 (coe v0)
                                                                (coe v6))) in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                     v10 v9 v11
                                                     (coe
                                                        du_sound'45'sumTail_360 (coe v0) (coe v10)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                            -> case coe v4 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                   -> coe
                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500 v6
                                        v5 erased (coe du_sound'45'sumTail_360 (coe v0) (coe v6))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-sumTail
d_sound'45'sumTail_360 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_372
d_sound'45'sumTail_360 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'sumTail_360 v0 v2
du_sound'45'sumTail_360 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_372
du_sound'45'sumTail_360 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1) in
              coe
                (let v4
                       = coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0
                           (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> let v10
                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                   (coe v0) (coe v6) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14
                                                                = coe
                                                                    du_sound'45'prod_326 (coe v0)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                       (coe v1)) in
                                                          coe
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'plus_520
                                                               v13 v12 v14
                                                               (coe
                                                                  du_sound'45'sumTail_360 (coe v0)
                                                                  (coe v13)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                     (coe v0) (coe v3) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                         -> let v9
                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                      (coe v0) (coe v7) (coe v8) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> case coe v10 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                          -> let v13
                                                                   = coe
                                                                       du_sound'45'prod_326 (coe v0)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                          (coe v1)) in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'plus_520
                                                                  v12 v11 v13
                                                                  (coe
                                                                     du_sound'45'sumTail_360
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
                                                             du_sound'45'prod_326 (coe v0)
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                (coe v1)) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'plus_520
                                                        v8 v7 v9
                                                        (coe
                                                           du_sound'45'sumTail_360 (coe v0)
                                                           (coe v8)))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'done_506)
-- Once.Parser.Generic.Sound.Make.sound-type
d_sound'45'type_370 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374
d_sound'45'type_370 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'type_370 v0 v1
du_sound'45'type_370 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374
du_sound'45'type_370 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8
                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                      (coe v0) (coe v4) (coe v6) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> let v12
                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
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
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_446
                                                                                        v7 in
                                                                              coe
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                   v6 v4 v16
                                                                                   (coe
                                                                                      du_sound'45'prodTail_338
                                                                                      (coe v0)
                                                                                      (coe v6))) in
                                                                      coe
                                                                        (coe
                                                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                           v11 v10 v16
                                                                           (coe
                                                                              du_sound'45'sumTail_360
                                                                              (coe v0)
                                                                              (coe v11))) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                                   v15 v14 v16
                                                                   (coe
                                                                      du_sound'45'arrowTail_382
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
                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                      v11 v10 erased
                                                      (coe
                                                         du_sound'45'arrowTail_382 (coe v0)
                                                         (coe v11))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                        (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7
                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                         (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
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
                                                                                           du_sound'45'kw_316
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v1) in
                                                                                 coe
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                      v6 v5 v15
                                                                                      (coe
                                                                                         du_sound'45'prodTail_338
                                                                                         (coe v0)
                                                                                         (coe
                                                                                            v6))) in
                                                                         coe
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                              v10 v9 v15
                                                                              (coe
                                                                                 du_sound'45'sumTail_360
                                                                                 (coe v0)
                                                                                 (coe v10))) in
                                                                 coe
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                                      v14 v13 v15
                                                                      (coe
                                                                         du_sound'45'arrowTail_382
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
                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                         v10 v9 erased
                                                         (coe
                                                            du_sound'45'arrowTail_382 (coe v0)
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
                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                (coe v0) (coe v5) (coe v6) in
                                      coe
                                        (case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                             -> case coe v8 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                    -> coe
                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                         v10 v9 erased
                                                         (coe
                                                            du_sound'45'arrowTail_382 (coe v0)
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
                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                               v6 v5 erased
                                               (coe du_sound'45'arrowTail_382 (coe v0) (coe v6))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-arrowTail
d_sound'45'arrowTail_382 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_376
d_sound'45'arrowTail_382 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'arrowTail_382 v0 v2
du_sound'45'arrowTail_382 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_376
du_sound'45'arrowTail_382 v0 v1
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
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0
                           (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34 (coe v1)) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                      -> let v11
                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                   (coe v0) (coe v7) (coe v9) in
                                         coe
                                           (case coe v11 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                -> case coe v12 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                       -> let v15
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                    (coe v0) (coe v13) (coe v14) in
                                                          coe
                                                            (case coe v15 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                 -> case coe v16 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                        -> let v19
                                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
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
                                                                                                      du_sound'45'type_370
                                                                                                      (coe
                                                                                                         v0)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                         (coe
                                                                                                            v1)) in
                                                                                            coe
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                                                                                            du_sound'45'type_370
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                           (coe v0) (coe v13)
                                                                           (coe v14) in
                                                                 coe
                                                                   (case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                               -> let v19
                                                                                        = coe
                                                                                            du_sound'45'type_370
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                                                                                  du_sound'45'type_370
                                                                                  (coe v0)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                     (coe v1)) in
                                                                        coe
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
                                                                             v13 v3 v15)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v6
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                     (coe v0) (coe v4) in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                  -> case coe v7 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                         -> let v10
                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                      (coe v0) (coe v8) (coe v9) in
                                            coe
                                              (case coe v10 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                   -> case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                          -> let v14
                                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                       (coe v0) (coe v12)
                                                                       (coe v13) in
                                                             coe
                                                               (case coe v14 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                    -> case coe v15 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                           -> let v18
                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
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
                                                                                                         du_sound'45'type_370
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                            (coe
                                                                                                               v1)) in
                                                                                               coe
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                                                                                               du_sound'45'type_370
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                              (coe v0) (coe v12)
                                                                              (coe v13) in
                                                                    coe
                                                                      (case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                           -> case coe v15 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                  -> let v18
                                                                                           = coe
                                                                                               du_sound'45'type_370
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                                                                                     du_sound'45'type_370
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                             (coe v0) (coe v8) (coe v9) in
                                                   coe
                                                     (case coe v10 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                          -> case coe v11 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                 -> let v14
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                              (coe v0) (coe v12)
                                                                              (coe v13) in
                                                                    coe
                                                                      (case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                           -> case coe v15 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                  -> let v18
                                                                                           = coe
                                                                                               du_sound'45'type_370
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                                                                                     du_sound'45'type_370
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                    (coe v0) (coe v8) (coe v9) in
                                                          coe
                                                            (case coe v10 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                                 -> case coe v11 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                        -> let v14
                                                                                 = coe
                                                                                     du_sound'45'type_370
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                                                                           du_sound'45'type_370
                                                                           (coe v0)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34
                                                                              (coe v1)) in
                                                                 coe
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_550
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
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0
                           (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> let v10
                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                   (coe v0) (coe v6) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                    (coe v0) (coe v12) (coe v13) in
                                                          coe
                                                            (case coe v14 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                 -> case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                        -> let v18
                                                                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
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
                                                                                                      du_sound'45'type_370
                                                                                                      (coe
                                                                                                         v0)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                         (coe
                                                                                                            v1)) in
                                                                                            coe
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
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
                                                                                            du_sound'45'type_370
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
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
                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                           (coe v0) (coe v12)
                                                                           (coe v13) in
                                                                 coe
                                                                   (case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> let v18
                                                                                        = coe
                                                                                            du_sound'45'type_370
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                               (coe
                                                                                                  v1)) in
                                                                                  coe
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
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
                                                                                  du_sound'45'type_370
                                                                                  (coe v0)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                     (coe v1)) in
                                                                        coe
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
                                                                             v12 v14)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                     (coe v0) (coe v3) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                         -> let v9
                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                      (coe v0) (coe v7) (coe v8) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> case coe v10 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                          -> let v13
                                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                       (coe v0) (coe v11)
                                                                       (coe v12) in
                                                             coe
                                                               (case coe v13 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                    -> case coe v14 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                           -> let v17
                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
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
                                                                                                         du_sound'45'type_370
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                            (coe
                                                                                                               v1)) in
                                                                                               coe
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
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
                                                                                               du_sound'45'type_370
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
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
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                              (coe v0) (coe v11)
                                                                              (coe v12) in
                                                                    coe
                                                                      (case coe v13 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                           -> case coe v14 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                  -> let v17
                                                                                           = coe
                                                                                               du_sound'45'type_370
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
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
                                                                                     du_sound'45'type_370
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
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
                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                             (coe v0) (coe v7) (coe v8) in
                                                   coe
                                                     (case coe v9 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                          -> case coe v10 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                 -> let v13
                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                              (coe v0) (coe v11)
                                                                              (coe v12) in
                                                                    coe
                                                                      (case coe v13 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                           -> case coe v14 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                  -> let v17
                                                                                           = coe
                                                                                               du_sound'45'type_370
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                                  (coe
                                                                                                     v1)) in
                                                                                     coe
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
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
                                                                                     du_sound'45'type_370
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
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
                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
                                                                    (coe v0) (coe v7) (coe v8) in
                                                          coe
                                                            (case coe v9 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                 -> case coe v10 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                        -> let v13
                                                                                 = coe
                                                                                     du_sound'45'type_370
                                                                                     (coe v0)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                                        (coe v1)) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
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
                                                                           du_sound'45'type_370
                                                                           (coe v0)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                                              (coe v1)) in
                                                                 coe
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_560
                                                                      v7 v9)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         MAlonzo.Code.Once.Parser.Generic.Relation.C_adD_20
           -> coe MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'done_538
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-fAtom
d_sound'45'fAtom_392 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_378
d_sound'45'fAtom_392 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'fAtom_392 v0 v1
du_sound'45'fAtom_392 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_378
du_sound'45'fAtom_392 v0 v1
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
                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'id_564)
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
                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
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
                                                                                        du_sound'45'atom_306
                                                                                        (coe v0)
                                                                                        (coe v3) in
                                                                              coe
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'k_572
                                                                                   v13 v17)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                             -> let v12
                                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                          (coe v0) (coe v3) in
                                                                coe
                                                                  (case coe v12 of
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                       -> case coe v13 of
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                              -> let v16
                                                                                       = coe
                                                                                           du_sound'45'atom_306
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v3) in
                                                                                 coe
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'k_572
                                                                                      v14 v16)
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                           _ -> MAlonzo.RTE.mazUnreachableError)))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError))
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> let v4
                        = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_90
                            (coe v0) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> let v8
                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_96
                                             (coe v0) (coe v6) (coe v7) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> let v12
                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_98
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
                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_582
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                    (coe v17))
                                                                                 (coe
                                                                                    du_sound'45'fSum_424
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
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_582
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                          (coe v13))
                                                                       (coe
                                                                          du_sound'45'fSum_424
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
                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_98
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
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_582
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                          (coe v13))
                                                                       (coe
                                                                          du_sound'45'fSum_424
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
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_582
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                (coe v9))
                                                             (coe
                                                                du_sound'45'fSum_424 (coe v0)
                                                                (coe v3)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-fProd
d_sound'45'fProd_402 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_380
d_sound'45'fProd_402 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'fProd_402 v0 v1
du_sound'45'fProd_402 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_380
du_sound'45'fProd_402 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_90
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> let v6 = coe du_sound'45'fAtom_392 (coe v0) (coe v1) in
                     coe
                       (coe
                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pfp'45'mk_594 v5 v4 v6
                          (coe du_sound'45'fProdTail_414 (coe v0) (coe v5)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-fProdTail
d_sound'45'fProdTail_414 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_382
d_sound'45'fProdTail_414 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'fProdTail_414 v0 v2
du_sound'45'fProdTail_414 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_382
du_sound'45'fProdTail_414 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_90
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
                                         du_sound'45'fAtom_392 (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                            (coe v1)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pfpt'45'star_614 v6
                                    v5 v7 (coe du_sound'45'fProdTail_414 (coe v0) (coe v6)))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_pfpt'45'done_600)
-- Once.Parser.Generic.Sound.Make.sound-fSum
d_sound'45'fSum_424 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_384
d_sound'45'fSum_424 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'fSum_424 v0 v1
du_sound'45'fSum_424 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_384
du_sound'45'fSum_424 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_90
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> let v6
                           = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_96
                               (coe v0) (coe v4) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                   -> let v10
                                            = let v10
                                                    = coe du_sound'45'fAtom_392 (coe v0) (coe v1) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pfp'45'mk_594
                                                   v5 v4 v10
                                                   (coe
                                                      du_sound'45'fProdTail_414 (coe v0)
                                                      (coe v5))) in
                                      coe
                                        (coe
                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfs'45'mk_626
                                           v9 v8 v10
                                           (coe du_sound'45'fSumTail_436 (coe v0) (coe v9)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                         -> coe
                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pfs'45'mk_626 v5 v4
                              erased (coe du_sound'45'fSumTail_436 (coe v0) (coe v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Sound.Make.sound-fSumTail
d_sound'45'fSumTail_436 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_386
d_sound'45'fSumTail_436 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'fSumTail_436 v0 v2
du_sound'45'fSumTail_436 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_386
du_sound'45'fSumTail_436 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v1) in
    coe
      (if coe v2
         then let v3
                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_90
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7
                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_96
                                         (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = coe
                                                          du_sound'45'fProd_402 (coe v0)
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                             (coe v1)) in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'plus_646
                                                     v10 v9 v11
                                                     (coe
                                                        du_sound'45'fSumTail_436 (coe v0)
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
                                                du_sound'45'fProd_402 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24
                                                   (coe v1)) in
                                      coe
                                        (coe
                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'plus_646
                                           v6 v5 v7
                                           (coe du_sound'45'fSumTail_436 (coe v0) (coe v6)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         else coe
                MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'done_632)
