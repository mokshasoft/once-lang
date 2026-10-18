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
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Parser.Generic.Complete.Make._.ParsesArrowTailG
d_ParsesArrowTailG_78 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesAtomG
d_ParsesAtomG_80 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncAtomG
d_ParsesFuncAtomG_82 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncProdG
d_ParsesFuncProdG_84 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_86 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncSumG
d_ParsesFuncSumG_88 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_90 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesProdG
d_ParsesProdG_92 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesProdTailG
d_ParsesProdTailG_94 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesSumG
d_ParsesSumG_96 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesSumTailG
d_ParsesSumTailG_98 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesTypeG
d_ParsesTypeG_100 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.arrowTailP
d_arrowTailP_272 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_272 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_110 (coe v0)
-- Once.Parser.Generic.Complete.Make._.atomP
d_atomP_276 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_276 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_98 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fAtomP
d_fAtomP_278 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_278 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_112 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fProdP
d_fProdP_280 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_280 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_114 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fProdTailP
d_fProdTailP_282 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_282 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_118 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fSumP
d_fSumP_284 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_284 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_116 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fSumTailP
d_fSumTailP_286 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_286 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_120 (coe v0)
-- Once.Parser.Generic.Complete.Make._.prodP
d_prodP_296 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_296 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_100 (coe v0)
-- Once.Parser.Generic.Complete.Make._.prodTailP
d_prodTailP_298 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_298 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_106 (coe v0)
-- Once.Parser.Generic.Complete.Make._.sumP
d_sumP_300 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_300 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_102 (coe v0)
-- Once.Parser.Generic.Complete.Make._.sumTailP
d_sumTailP_302 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_302 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_108 (coe v0)
-- Once.Parser.Generic.Complete.Make._.typeP
d_typeP_304 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_304 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_104 (coe v0)
-- Once.Parser.Generic.Complete.Make.fSum-parenAct
d_fSum'45'parenAct_308 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenAct_308 = erased
-- Once.Parser.Generic.Complete.Make.complete-atom
d_complete'45'atom_318 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_318 = erased
-- Once.Parser.Generic.Complete.Make.complete-prod
d_complete'45'prod_326 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_326 = erased
-- Once.Parser.Generic.Complete.Make.complete-prodTail
d_complete'45'prodTail_336 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_336 = erased
-- Once.Parser.Generic.Complete.Make.complete-sum
d_complete'45'sum_344 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_344 = erased
-- Once.Parser.Generic.Complete.Make.complete-sumTail
d_complete'45'sumTail_354 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_354 = erased
-- Once.Parser.Generic.Complete.Make.complete-type
d_complete'45'type_362 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_362 = erased
-- Once.Parser.Generic.Complete.Make.complete-arrowTail
d_complete'45'arrowTail_372 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_372 = erased
-- Once.Parser.Generic.Complete.Make.complete-fAtom
d_complete'45'fAtom_380 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_380 = erased
-- Once.Parser.Generic.Complete.Make.complete-fProd
d_complete'45'fProd_388 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_388 = erased
-- Once.Parser.Generic.Complete.Make.complete-fProdTail
d_complete'45'fProdTail_398 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_398 = erased
-- Once.Parser.Generic.Complete.Make.complete-fSum
d_complete'45'fSum_406 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_406 = erased
-- Once.Parser.Generic.Complete.Make.complete-fSumTail
d_complete'45'fSumTail_416 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_416 = erased
