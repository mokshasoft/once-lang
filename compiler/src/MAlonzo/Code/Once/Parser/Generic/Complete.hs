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
d_ParsesArrowTailG_80 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesAtomG
d_ParsesAtomG_82 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncAtomG
d_ParsesFuncAtomG_84 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncProdG
d_ParsesFuncProdG_86 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_88 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncSumG
d_ParsesFuncSumG_90 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_92 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesProdG
d_ParsesProdG_94 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesProdTailG
d_ParsesProdTailG_96 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesSumG
d_ParsesSumG_98 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesSumTailG
d_ParsesSumTailG_100 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesTypeG
d_ParsesTypeG_102 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.arrowTailP
d_arrowTailP_278 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_278 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_134 (coe v0)
-- Once.Parser.Generic.Complete.Make._.atomP
d_atomP_282 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_282 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_122 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fAtomP
d_fAtomP_284 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_284 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_136 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fProdP
d_fProdP_286 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_286 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_138 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fProdTailP
d_fProdTailP_288 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_288 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_142 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fSumP
d_fSumP_290 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_290 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_140 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fSumTailP
d_fSumTailP_292 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_292 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_144 (coe v0)
-- Once.Parser.Generic.Complete.Make._.prodP
d_prodP_308 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_308 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_124 (coe v0)
-- Once.Parser.Generic.Complete.Make._.prodTailP
d_prodTailP_310 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_310 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_130 (coe v0)
-- Once.Parser.Generic.Complete.Make._.sumP
d_sumP_312 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_312 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_126 (coe v0)
-- Once.Parser.Generic.Complete.Make._.sumTailP
d_sumTailP_314 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_314 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_132 (coe v0)
-- Once.Parser.Generic.Complete.Make._.typeP
d_typeP_316 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_316 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_128 (coe v0)
-- Once.Parser.Generic.Complete.Make.fSum-parenEff
d_fSum'45'parenEff_320 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenEff_320 = erased
-- Once.Parser.Generic.Complete.Make.fSum-parenAct
d_fSum'45'parenAct_326 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenAct_326 = erased
-- Once.Parser.Generic.Complete.Make.complete-atom
d_complete'45'atom_336 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_336 = erased
-- Once.Parser.Generic.Complete.Make.complete-prod
d_complete'45'prod_344 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_344 = erased
-- Once.Parser.Generic.Complete.Make.complete-prodTail
d_complete'45'prodTail_354 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_370 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_354 = erased
-- Once.Parser.Generic.Complete.Make.complete-sum
d_complete'45'sum_362 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_372 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_362 = erased
-- Once.Parser.Generic.Complete.Make.complete-sumTail
d_complete'45'sumTail_372 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_372 = erased
-- Once.Parser.Generic.Complete.Make.complete-type
d_complete'45'type_380 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_380 = erased
-- Once.Parser.Generic.Complete.Make.complete-arrowTail
d_complete'45'arrowTail_390 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_390 = erased
-- Once.Parser.Generic.Complete.Make.complete-fAtom
d_complete'45'fAtom_398 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_398 = erased
-- Once.Parser.Generic.Complete.Make.complete-fProd
d_complete'45'fProd_406 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_406 = erased
-- Once.Parser.Generic.Complete.Make.complete-fProdTail
d_complete'45'fProdTail_416 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_416 = erased
-- Once.Parser.Generic.Complete.Make.complete-fSum
d_complete'45'fSum_424 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_424 = erased
-- Once.Parser.Generic.Complete.Make.complete-fSumTail
d_complete'45'fSumTail_434 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_388 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_434 = erased
