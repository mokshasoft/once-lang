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

module MAlonzo.Code.Once.Parser.Generic.Complete where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type

-- Once.Parser.Generic.Complete.Make._.ParsesArrowTailG
d_ParsesArrowTailG_82 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesAtomG
d_ParsesAtomG_84 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncAtomG
d_ParsesFuncAtomG_86 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncProdG
d_ParsesFuncProdG_88 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_90 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncSumG
d_ParsesFuncSumG_92 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_94 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesProdG
d_ParsesProdG_96 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesProdTailG
d_ParsesProdTailG_98 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesSumG
d_ParsesSumG_100 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesSumTailG
d_ParsesSumTailG_102 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesTypeG
d_ParsesTypeG_104 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.arrowTailP
d_arrowTailP_280 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_280 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_92 (coe v0)
-- Once.Parser.Generic.Complete.Make._.atomP
d_atomP_284 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_284 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_80 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fAtomP
d_fAtomP_286 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_286 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_94 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fProdP
d_fProdP_288 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_288 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_96 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fProdTailP
d_fProdTailP_290 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_290 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_100 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fSumP
d_fSumP_292 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_292 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_98 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fSumTailP
d_fSumTailP_294 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_294 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_102 (coe v0)
-- Once.Parser.Generic.Complete.Make._.prodP
d_prodP_296 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_296 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_82 (coe v0)
-- Once.Parser.Generic.Complete.Make._.prodTailP
d_prodTailP_298 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_298 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_88 (coe v0)
-- Once.Parser.Generic.Complete.Make._.sumP
d_sumP_300 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_300 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_84 (coe v0)
-- Once.Parser.Generic.Complete.Make._.sumTailP
d_sumTailP_302 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_302 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_90 (coe v0)
-- Once.Parser.Generic.Complete.Make._.typeP
d_typeP_304 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_304 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_86 (coe v0)
-- Once.Parser.Generic.Complete.Make.complete-atom
d_complete'45'atom_312 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_312 = erased
-- Once.Parser.Generic.Complete.Make.complete-prod
d_complete'45'prod_320 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_320 = erased
-- Once.Parser.Generic.Complete.Make.complete-prodTail
d_complete'45'prodTail_330 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_330 = erased
-- Once.Parser.Generic.Complete.Make.complete-sum
d_complete'45'sum_338 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_338 = erased
-- Once.Parser.Generic.Complete.Make.complete-sumTail
d_complete'45'sumTail_348 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_388 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_348 = erased
-- Once.Parser.Generic.Complete.Make.complete-type
d_complete'45'type_356 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_390 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_356 = erased
-- Once.Parser.Generic.Complete.Make.complete-arrowTail
d_complete'45'arrowTail_366 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_392 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_366 = erased
-- Once.Parser.Generic.Complete.Make.complete-fAtom
d_complete'45'fAtom_374 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_374 = erased
-- Once.Parser.Generic.Complete.Make.complete-fProd
d_complete'45'fProd_382 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_382 = erased
-- Once.Parser.Generic.Complete.Make.complete-fProdTail
d_complete'45'fProdTail_392 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_398 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_392 = erased
-- Once.Parser.Generic.Complete.Make.complete-fSum
d_complete'45'fSum_400 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_400 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_400 = erased
-- Once.Parser.Generic.Complete.Make.complete-fSumTail
d_complete'45'fSumTail_410 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_410 = erased
