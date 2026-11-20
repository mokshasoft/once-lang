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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.Parser.Generic.Complete.forget-under
d_forget'45'under_18 ::
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forget'45'under_18 = erased
-- Once.Parser.Generic.Complete.forget-after
d_forget'45'after_34 ::
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forget'45'after_34 = erased
-- Once.Parser.Generic.Complete.forget-weaken
d_forget'45'weaken_46 ::
  () ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forget'45'weaken_46 = erased
-- Once.Parser.Generic.Complete.map-just
d_map'45'just_62 ::
  () ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'just_62 = erased
-- Once.Parser.Generic.Complete.Make._.ParsesArrowTailG
d_ParsesArrowTailG_136 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesAtomG
d_ParsesAtomG_138 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncAtomG
d_ParsesFuncAtomG_140 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncProdG
d_ParsesFuncProdG_142 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_144 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncSumG
d_ParsesFuncSumG_146 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_148 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesProdG
d_ParsesProdG_150 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesProdTailG
d_ParsesProdTailG_152 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesSumG
d_ParsesSumG_154 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesSumTailG
d_ParsesSumTailG_156 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Complete.Make._.ParsesTypeG
d_ParsesTypeG_158 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Complete.Make._.arrK
d_arrK_330 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrK_330 ~v0 = du_arrK_330
du_arrK_330 ::
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_arrK_330 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_arrK_444 v0 v2 v3 v4
-- Once.Parser.Generic.Complete.Make._.arrowTailA
d_arrowTailA_332 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailA_332 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_arrowTailA_564 (coe v0)
      v1 v2
-- Once.Parser.Generic.Complete.Make._.arrowTailP
d_arrowTailP_334 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_334 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_1116 (coe v0)
-- Once.Parser.Generic.Complete.Make._.atGo
d_atGo_336 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atGo_336 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atGo_572 (coe v0) v1 v2
      v3 v4 v5
-- Once.Parser.Generic.Complete.Make._.atomA
d_atomA_338 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomA_338 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomA_470 (coe v0) v1
-- Once.Parser.Generic.Complete.Make._.atomKw
d_atomKw_342 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_342 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomKw_482 (coe v0) v1
-- Once.Parser.Generic.Complete.Make._.atomP
d_atomP_344 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_344 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_1096 (coe v0)
-- Once.Parser.Generic.Complete.Make._.atomX
d_atomX_346 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomX_346 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomX_478 (coe v0) v1 v3
-- Once.Parser.Generic.Complete.Make._.fAtomA
d_fAtomA_348 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomA_348 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fAtomA_576 (coe v0) v1
-- Once.Parser.Generic.Complete.Make._.fAtomP
d_fAtomP_352 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_352 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_1130 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fProdA
d_fProdA_354 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdA_354 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdA_590 (coe v0) v1
-- Once.Parser.Generic.Complete.Make._.fProdK
d_fProdK_356 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdK_356 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdK_594 (coe v0) v2
-- Once.Parser.Generic.Complete.Make._.fProdP
d_fProdP_358 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_358 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_1132 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fProdTailA
d_fProdTailA_360 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailA_360 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdTailA_598 (coe v0)
      v1 v2
-- Once.Parser.Generic.Complete.Make._.fProdTailP
d_fProdTailP_362 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_362 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_1142 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fSumA
d_fSumA_364 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumA_364 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumA_612 (coe v0) v1
-- Once.Parser.Generic.Complete.Make._.fSumK
d_fSumK_366 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumK_366 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumK_616 (coe v0) v2
-- Once.Parser.Generic.Complete.Make._.fSumP
d_fSumP_368 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_368 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_1134 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fSumTailA
d_fSumTailA_370 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailA_370 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumTailA_620 (coe v0)
      v1 v2
-- Once.Parser.Generic.Complete.Make._.fSumTailP
d_fSumTailP_372 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_372 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_1144 (coe v0)
-- Once.Parser.Generic.Complete.Make._.fptGo
d_fptGo_376 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fptGo_376 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fptGo_604 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Complete.Make._.fptK
d_fptK_378 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fptK_378 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fptK_608 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Complete.Make._.fstGo
d_fstGo_380 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fstGo_380 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fstGo_626 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Complete.Make._.fstK
d_fstK_382 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fstK_382 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fstK_630 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Complete.Make._.nuAct
d_nuAct_386 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuAct_386 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuAct_508 (coe v0) v3
-- Once.Parser.Generic.Complete.Make._.nuClose
d_nuClose_390 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuClose_390 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuClose_386 (coe v0)
-- Once.Parser.Generic.Complete.Make._.nuTry
d_nuTry_392 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuTry_392 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuTry_502 (coe v0) v1 v3
-- Once.Parser.Generic.Complete.Make._.parenK
d_parenK_396 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parenK_396 ~v0 = du_parenK_396
du_parenK_396 ::
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parenK_396 v0 v1 v2
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.du_parenK_428 v1 v2
-- Once.Parser.Generic.Complete.Make._.prodA
d_prodA_398 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodA_398 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_prodA_512 (coe v0) v1
-- Once.Parser.Generic.Complete.Make._.prodK
d_prodK_400 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodK_400 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_prodK_516 (coe v0) v2
-- Once.Parser.Generic.Complete.Make._.prodP
d_prodP_402 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_402 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_1098 (coe v0)
-- Once.Parser.Generic.Complete.Make._.prodTailA
d_prodTailA_404 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailA_404 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_prodTailA_520 (coe v0)
      v1 v2
-- Once.Parser.Generic.Complete.Make._.prodTailP
d_prodTailP_406 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_406 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_1112 (coe v0)
-- Once.Parser.Generic.Complete.Make._.ptGo
d_ptGo_408 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ptGo_408 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_ptGo_526 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Complete.Make._.ptK
d_ptK_410 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ptK_410 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_ptK_530 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Complete.Make._.stGo
d_stGo_412 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stGo_412 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_stGo_548 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Complete.Make._.stK
d_stK_414 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stK_414 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_stK_552 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Complete.Make._.sumA
d_sumA_416 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumA_416 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_sumA_534 (coe v0) v1
-- Once.Parser.Generic.Complete.Make._.sumK
d_sumK_418 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumK_418 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_sumK_538 (coe v0) v2
-- Once.Parser.Generic.Complete.Make._.sumP
d_sumP_420 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_420 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_1100 (coe v0)
-- Once.Parser.Generic.Complete.Make._.sumTailA
d_sumTailA_422 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailA_422 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_sumTailA_542 (coe v0) v1
      v2
-- Once.Parser.Generic.Complete.Make._.sumTailP
d_sumTailP_424 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_424 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_1114 (coe v0)
-- Once.Parser.Generic.Complete.Make._.twoK
d_twoK_426 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_twoK_426 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_twoK_498 (coe v0) v1 v3
      v4
-- Once.Parser.Generic.Complete.Make._.typeA
d_typeA_428 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeA_428 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_typeA_556 (coe v0) v1
-- Once.Parser.Generic.Complete.Make._.typeK
d_typeK_430 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeK_430 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_typeK_560 (coe v0) v2
-- Once.Parser.Generic.Complete.Make._.typeP
d_typeP_432 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_432 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_1102 (coe v0)
-- Once.Parser.Generic.Complete.Make.atomX-miss
d_atomX'45'miss_440 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atomX'45'miss_440 = erased
-- Once.Parser.Generic.Complete.Make.atomX-hit
d_atomX'45'hit_458 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atomX'45'hit_458 = erased
-- Once.Parser.Generic.Complete.Make.parenK-ok
d_parenK'45'ok_476 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parenK'45'ok_476 = erased
-- Once.Parser.Generic.Complete.Make.twoK-ok
d_twoK'45'ok_506 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_twoK'45'ok_506 = erased
-- Once.Parser.Generic.Complete.Make.nuTry-just
d_nuTry'45'just_534 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nuTry'45'just_534 = erased
-- Once.Parser.Generic.Complete.Make.nuTry-nothing
d_nuTry'45'nothing_552 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nuTry'45'nothing_552 = erased
-- Once.Parser.Generic.Complete.Make.nuClose-ok
d_nuClose'45'ok_566 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nuClose'45'ok_566 = erased
-- Once.Parser.Generic.Complete.Make.fSum-parenAct
d_fSum'45'parenAct_580 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenAct_580 = erased
-- Once.Parser.Generic.Complete.Make.prodK-ok
d_prodK'45'ok_602 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prodK'45'ok_602 = erased
-- Once.Parser.Generic.Complete.Make.ptGo-done
d_ptGo'45'done_626 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ptGo'45'done_626 = erased
-- Once.Parser.Generic.Complete.Make.ptK-ok
d_ptK'45'ok_656 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ptK'45'ok_656 = erased
-- Once.Parser.Generic.Complete.Make.ptGo-star
d_ptGo'45'star_696 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ptGo'45'star_696 = erased
-- Once.Parser.Generic.Complete.Make.sumK-ok
d_sumK'45'ok_726 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sumK'45'ok_726 = erased
-- Once.Parser.Generic.Complete.Make.stGo-done
d_stGo'45'done_750 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stGo'45'done_750 = erased
-- Once.Parser.Generic.Complete.Make.stK-ok
d_stK'45'ok_780 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stK'45'ok_780 = erased
-- Once.Parser.Generic.Complete.Make.stGo-plus
d_stGo'45'plus_820 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stGo'45'plus_820 = erased
-- Once.Parser.Generic.Complete.Make.typeK-ok
d_typeK'45'ok_850 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_typeK'45'ok_850 = erased
-- Once.Parser.Generic.Complete.Make.arrK-ok
d_arrK'45'ok_878 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arrK'45'ok_878 = erased
-- Once.Parser.Generic.Complete.Make.atGo-done
d_atGo'45'done_908 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atGo'45'done_908 = erased
-- Once.Parser.Generic.Complete.Make.atGo-A
d_atGo'45'A_940 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atGo'45'A_940 = erased
-- Once.Parser.Generic.Complete.Make.atGo-G
d_atGo'45'G_976 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atGo'45'G_976 = erased
-- Once.Parser.Generic.Complete.Make.fProdK-ok
d_fProdK'45'ok_1006 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fProdK'45'ok_1006 = erased
-- Once.Parser.Generic.Complete.Make.fptGo-done
d_fptGo'45'done_1030 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fptGo'45'done_1030 = erased
-- Once.Parser.Generic.Complete.Make.fptK-ok
d_fptK'45'ok_1060 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fptK'45'ok_1060 = erased
-- Once.Parser.Generic.Complete.Make.fptGo-star
d_fptGo'45'star_1100 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fptGo'45'star_1100 = erased
-- Once.Parser.Generic.Complete.Make.fSumK-ok
d_fSumK'45'ok_1130 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSumK'45'ok_1130 = erased
-- Once.Parser.Generic.Complete.Make.fstGo-done
d_fstGo'45'done_1154 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fstGo'45'done_1154 = erased
-- Once.Parser.Generic.Complete.Make.fstK-ok
d_fstK'45'ok_1184 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fstK'45'ok_1184 = erased
-- Once.Parser.Generic.Complete.Make.fstGo-plus
d_fstGo'45'plus_1224 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fstGo'45'plus_1224 = erased
-- Once.Parser.Generic.Complete.Make.complete-atomA
d_complete'45'atomA_1246 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atomA_1246 = erased
-- Once.Parser.Generic.Complete.Make.complete-prodA
d_complete'45'prodA_1256 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodA_1256 = erased
-- Once.Parser.Generic.Complete.Make.complete-prodTailA
d_complete'45'prodTailA_1268 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTailA_1268 = erased
-- Once.Parser.Generic.Complete.Make.complete-sumA
d_complete'45'sumA_1278 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumA_1278 = erased
-- Once.Parser.Generic.Complete.Make.complete-sumTailA
d_complete'45'sumTailA_1290 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTailA_1290 = erased
-- Once.Parser.Generic.Complete.Make.complete-typeA
d_complete'45'typeA_1300 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'typeA_1300 = erased
-- Once.Parser.Generic.Complete.Make.complete-arrowTailA
d_complete'45'arrowTailA_1312 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTailA_1312 = erased
-- Once.Parser.Generic.Complete.Make.complete-fAtomA
d_complete'45'fAtomA_1322 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtomA_1322 = erased
-- Once.Parser.Generic.Complete.Make.complete-fProdA
d_complete'45'fProdA_1332 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdA_1332 = erased
-- Once.Parser.Generic.Complete.Make.complete-fProdTailA
d_complete'45'fProdTailA_1344 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTailA_1344 = erased
-- Once.Parser.Generic.Complete.Make.complete-fSumA
d_complete'45'fSumA_1354 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumA_1354 = erased
-- Once.Parser.Generic.Complete.Make.complete-fSumTailA
d_complete'45'fSumTailA_1366 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTailA_1366 = erased
-- Once.Parser.Generic.Complete.Make.complete-atom
d_complete'45'atom_1542 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_1542 = erased
-- Once.Parser.Generic.Complete.Make.complete-prod
d_complete'45'prod_1552 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_1552 = erased
-- Once.Parser.Generic.Complete.Make.complete-prodTail
d_complete'45'prodTail_1564 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_1564 = erased
-- Once.Parser.Generic.Complete.Make.complete-sum
d_complete'45'sum_1574 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_1574 = erased
-- Once.Parser.Generic.Complete.Make.complete-sumTail
d_complete'45'sumTail_1586 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_1586 = erased
-- Once.Parser.Generic.Complete.Make.complete-type
d_complete'45'type_1596 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_1596 = erased
-- Once.Parser.Generic.Complete.Make.complete-arrowTail
d_complete'45'arrowTail_1608 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_1608 = erased
-- Once.Parser.Generic.Complete.Make.complete-fAtom
d_complete'45'fAtom_1618 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_1618 = erased
-- Once.Parser.Generic.Complete.Make.complete-fProd
d_complete'45'fProd_1628 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_1628 = erased
-- Once.Parser.Generic.Complete.Make.complete-fProdTail
d_complete'45'fProdTail_1640 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_1640 = erased
-- Once.Parser.Generic.Complete.Make.complete-fSum
d_complete'45'fSum_1650 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_1650 = erased
-- Once.Parser.Generic.Complete.Make.complete-fSumTail
d_complete'45'fSumTail_1662 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_1662 = erased
