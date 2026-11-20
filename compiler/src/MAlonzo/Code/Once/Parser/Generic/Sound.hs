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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.Parser.Generic.Sound.map-sound
d_map'45'sound_28 ::
  () ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()) ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_map'45'sound_28 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_map'45'sound_28 v4 v8
du_map'45'sound_28 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny
du_map'45'sound_28 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe v1 v3 v5 erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.under-inv
d_under'45'inv_56 ::
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_under'45'inv_56 = erased
-- Once.Parser.Generic.Sound.Make._.ParsesArrowTailG
d_ParsesArrowTailG_134 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesAtomG
d_ParsesAtomG_136 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncAtomG
d_ParsesFuncAtomG_138 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncProdG
d_ParsesFuncProdG_140 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_142 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncSumG
d_ParsesFuncSumG_144 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_146 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesProdG
d_ParsesProdG_148 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesProdTailG
d_ParsesProdTailG_150 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesSumG
d_ParsesSumG_152 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesSumTailG
d_ParsesSumTailG_154 a0 a1 a2 a3 a4 = ()
-- Once.Parser.Generic.Sound.Make._.ParsesTypeG
d_ParsesTypeG_156 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.Sound.Make._.arrK
d_arrK_328 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrK_328 ~v0 = du_arrK_328
du_arrK_328 ::
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_arrK_328 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_arrK_444 v0 v2 v3 v4
-- Once.Parser.Generic.Sound.Make._.arrowTailA
d_arrowTailA_330 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailA_330 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_arrowTailA_564 (coe v0)
      v1 v2
-- Once.Parser.Generic.Sound.Make._.atGo
d_atGo_334 ::
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
d_atGo_334 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atGo_572 (coe v0) v1 v2
      v3 v4 v5
-- Once.Parser.Generic.Sound.Make._.atomA
d_atomA_336 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomA_336 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomA_470 (coe v0) v1
-- Once.Parser.Generic.Sound.Make._.atomH
d_atomH_338 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_HeadV_246 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomH_338 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomH_486 (coe v0) v1 v2
-- Once.Parser.Generic.Sound.Make._.atomKw
d_atomKw_340 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_340 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomKw_482 (coe v0) v1
-- Once.Parser.Generic.Sound.Make._.atomP
d_atomP_342 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_342 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_1096 (coe v0)
-- Once.Parser.Generic.Sound.Make._.atomX
d_atomX_344 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomX_344 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomX_478 (coe v0) v1 v3
-- Once.Parser.Generic.Sound.Make._.fAtomA
d_fAtomA_346 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomA_346 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fAtomA_576 (coe v0) v1
-- Once.Parser.Generic.Sound.Make._.fAtomH
d_fAtomH_348 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_HeadV_246 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomH_348 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fAtomH_580 (coe v0) v1
      v2
-- Once.Parser.Generic.Sound.Make._.fProdA
d_fProdA_352 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdA_352 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdA_590 (coe v0) v1
-- Once.Parser.Generic.Sound.Make._.fProdK
d_fProdK_354 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdK_354 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdK_594 (coe v0) v2
-- Once.Parser.Generic.Sound.Make._.fProdTailA
d_fProdTailA_358 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailA_358 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdTailA_598 (coe v0)
      v1 v2
-- Once.Parser.Generic.Sound.Make._.fSumA
d_fSumA_362 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumA_362 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumA_612 (coe v0) v1
-- Once.Parser.Generic.Sound.Make._.fSumK
d_fSumK_364 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumK_364 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumK_616 (coe v0) v2
-- Once.Parser.Generic.Sound.Make._.fSumP
d_fSumP_366 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_366 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_1134 (coe v0)
-- Once.Parser.Generic.Sound.Make._.fSumTailA
d_fSumTailA_368 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailA_368 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumTailA_620 (coe v0)
      v1 v2
-- Once.Parser.Generic.Sound.Make._.fkwK
d_fkwK_372 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_FKwV_186 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fkwK_372 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fkwK_586 (coe v0) v2 v3
-- Once.Parser.Generic.Sound.Make._.fptGo
d_fptGo_374 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fptGo_374 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fptGo_604 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Sound.Make._.fptK
d_fptK_376 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fptK_376 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fptK_608 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Sound.Make._.fstGo
d_fstGo_378 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fstGo_378 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fstGo_626 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Sound.Make._.fstK
d_fstK_380 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fstK_380 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fstK_630 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Sound.Make._.kwK
d_kwK_382 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_KwV_124 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_kwK_382 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_kwK_492 (coe v0) v2 v3
-- Once.Parser.Generic.Sound.Make._.nuAct
d_nuAct_384 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuAct_384 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuAct_508 (coe v0) v3
-- Once.Parser.Generic.Sound.Make._.nuC
d_nuC_386 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_CloseV_274 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuC_386 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_nuC_366 (coe v0)
-- Once.Parser.Generic.Sound.Make._.nuClose
d_nuClose_388 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuClose_388 v0
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuClose_386 (coe v0)
-- Once.Parser.Generic.Sound.Make._.nuTry
d_nuTry_390 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuTry_390 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuTry_502 (coe v0) v1 v3
-- Once.Parser.Generic.Sound.Make._.parenC
d_parenC_392 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_CloseV_274 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parenC_392 ~v0 = du_parenC_392
du_parenC_392 ::
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_CloseV_274 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parenC_392 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_parenC_406 v1 v2 v3 v4
      v5
-- Once.Parser.Generic.Sound.Make._.parenK
d_parenK_394 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parenK_394 ~v0 = du_parenK_394
du_parenK_394 ::
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parenK_394 v0 v1 v2
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.du_parenK_428 v1 v2
-- Once.Parser.Generic.Sound.Make._.prodA
d_prodA_396 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodA_396 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_prodA_512 (coe v0) v1
-- Once.Parser.Generic.Sound.Make._.prodK
d_prodK_398 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodK_398 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_prodK_516 (coe v0) v2
-- Once.Parser.Generic.Sound.Make._.prodTailA
d_prodTailA_402 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailA_402 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_prodTailA_520 (coe v0)
      v1 v2
-- Once.Parser.Generic.Sound.Make._.ptGo
d_ptGo_406 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ptGo_406 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_ptGo_526 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Sound.Make._.ptK
d_ptK_408 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ptK_408 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_ptK_530 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Sound.Make._.stGo
d_stGo_410 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stGo_410 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_stGo_548 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Sound.Make._.stK
d_stK_412 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stK_412 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_stK_552 (coe v0) v1 v2
      v3 v4
-- Once.Parser.Generic.Sound.Make._.sumA
d_sumA_414 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumA_414 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_sumA_534 (coe v0) v1
-- Once.Parser.Generic.Sound.Make._.sumK
d_sumK_416 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumK_416 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_sumK_538 (coe v0) v2
-- Once.Parser.Generic.Sound.Make._.sumTailA
d_sumTailA_420 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailA_420 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_sumTailA_542 (coe v0) v1
      v2
-- Once.Parser.Generic.Sound.Make._.twoK
d_twoK_424 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_twoK_424 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_twoK_498 (coe v0) v1 v3
      v4
-- Once.Parser.Generic.Sound.Make._.typeA
d_typeA_426 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeA_426 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_typeA_556 (coe v0) v1
-- Once.Parser.Generic.Sound.Make._.typeK
d_typeK_428 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeK_428 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_typeK_560 (coe v0) v2
-- Once.Parser.Generic.Sound.Make._.typeP
d_typeP_430 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_430 v0
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_1102 (coe v0)
-- Once.Parser.Generic.Sound.Make.parenC-sound
d_parenC'45'sound_450 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  () ->
  (AgdaAny -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_CloseV_274 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_parenC'45'sound_450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10
                      ~v11
  = du_parenC'45'sound_450 v7 v10
du_parenC'45'sound_450 ::
  MAlonzo.Code.Once.Parser.Generic.Parser.T_CloseV_274 ->
  AgdaAny -> AgdaAny
du_parenC'45'sound_450 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.Parser.Generic.Sound.Make.parenK-sound
d_parenK'45'sound_488 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  () ->
  (AgdaAny -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_parenK'45'sound_488 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8
  = du_parenK'45'sound_488 v4 v7
du_parenK'45'sound_488 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny
du_parenK'45'sound_488 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_parenC'45'sound_450
                           (coe MAlonzo.Code.Once.Parser.Generic.Parser.d_closeV_286 (coe v5))
                           (coe v1 v3 v5 erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.nuC-sound
d_nuC'45'sound_522 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_CloseV_274 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_nuC'45'sound_522 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9
  = du_nuC'45'sound_522 v2 v5 v8
du_nuC'45'sound_522 ::
  AgdaAny ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_CloseV_274 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
du_nuC'45'sound_522 v0 v1 v2
  = coe
      seq (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu'45'act_446 v0
         v2)
-- Once.Parser.Generic.Sound.Make.nuClose-sound
d_nuClose'45'sound_556 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_nuClose'45'sound_556 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6
  = du_nuClose'45'sound_556 v2 v5
du_nuClose'45'sound_556 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
du_nuClose'45'sound_556 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_nuC'45'sound_522 (coe v3)
                           (coe MAlonzo.Code.Once.Parser.Generic.Parser.d_closeV_286 (coe v5))
                           (coe v1 v3 v5 erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.atomX-sound
d_atomX'45'sound_588 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_atomX'45'sound_588 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_atomX'45'sound_588 v3 v4 v5 v6 v7
du_atomX'45'sound_588 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
du_atomX'45'sound_588 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_454 v9
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3 v1 v2 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.arrK-sound
d_arrK'45'sound_630 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()) ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_arrK'45'sound_630 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_arrK'45'sound_630 v5 v9
du_arrK'45'sound_630 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny
du_arrK'45'sound_630 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe v1 v3 v5 erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.BG
d_BG_660 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 -> ()
d_BG_660 = erased
-- Once.Parser.Generic.Sound.Make.sound-atom
d_sound'45'atom_676 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_sound'45'atom_676 v0 v1 ~v2 v3 v4 ~v5
  = du_sound'45'atom_676 v0 v1 v3 v4
du_sound'45'atom_676 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
du_sound'45'atom_676 v0 v1 v2 v3
  = coe
      du_atomX'45'sound_588
      (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0 v1)
      (coe v2) (coe v3)
      (\ v4 v5 v6 ->
         coe
           du_atomH'45'sound_688 (coe v0) (coe v1)
           (coe MAlonzo.Code.Once.Parser.Generic.Parser.d_headV_264 (coe v1))
           v5)
      erased
-- Once.Parser.Generic.Sound.Make.atomH-sound
d_atomH'45'sound_688 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_HeadV_246 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_atomH'45'sound_688 v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_atomH'45'sound_688 v0 v1 v2 v5
du_atomH'45'sound_688 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_HeadV_246 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
du_atomH'45'sound_688 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Generic.Parser.C_hWord_252
        -> case coe v1 of
             (:) v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Parser.Token.C_TWord_8 v8
                      -> coe
                           du_kwK'45'sound_702 (coe v0) (coe v7)
                           (coe MAlonzo.Code.Once.Parser.Generic.Parser.d_kwV_182 (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.Generic.Parser.C_hParen_256
        -> case coe v1 of
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'paren_464
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v3))
                    (coe
                       du_parenK'45'sound_488
                       (coe
                          MAlonzo.Code.Once.Parser.Generic.Parser.du_typeA_556 (coe v0)
                          (coe v6))
                       (\ v7 v8 v9 -> coe du_sound'45'type_916 (coe v0) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.kwK-sound
d_kwK'45'sound_702 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_KwV_124 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_kwK'45'sound_702 v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_kwK'45'sound_702 v0 v2 v3
du_kwK'45'sound_702 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_KwV_124 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
du_kwK'45'sound_702 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Generic.Parser.C_vUnit_126
        -> coe MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'unit_386
      MAlonzo.Code.Once.Parser.Generic.Parser.C_vVoid_128
        -> coe MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'void_390
      MAlonzo.Code.Once.Parser.Generic.Parser.C_vInt_130
        -> coe MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'int_394
      MAlonzo.Code.Once.Parser.Generic.Parser.C_vFloat_132
        -> coe MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'float_398
      MAlonzo.Code.Once.Parser.Generic.Parser.C_vEff_134
        -> coe
             du_twoK'45'sound_730 (coe v0)
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_atomA_470 (coe v0)
                (coe v1))
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'eff_410 v3 v5 v6
                  v7 v8)
             (\ v3 v4 v5 -> coe du_sound'45'atom_676 (coe v0) (coe v1) v3 v4)
      MAlonzo.Code.Once.Parser.Generic.Parser.C_vAct_136
        -> coe
             du_twoK'45'sound_730 (coe v0)
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_atomA_470 (coe v0)
                (coe v1))
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'act_422 v3 v5 v6
                  v7 v8)
             (\ v3 v4 v5 -> coe du_sound'45'atom_676 (coe v0) (coe v1) v3 v4)
      MAlonzo.Code.Once.Parser.Generic.Parser.C_vMu_138
        -> coe
             du_map'45'sound_28
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumA_612 (coe v0)
                (coe v1))
             (coe
                (\ v3 v4 v5 ->
                   coe
                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'mu_430 v3
                     (coe du_sound'45'fSum_1082 (coe v0) (coe v1) (coe v3) (coe v4))))
      MAlonzo.Code.Once.Parser.Generic.Parser.C_vNu_140
        -> coe
             du_nuTry'45'sound_746 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumA_612 (coe v0)
                (coe v1))
             (\ v3 v4 v5 -> coe du_sound'45'fSum_1082 (coe v0) (coe v1) v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.twoK-sound
d_twoK'45'sound_730 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_twoK'45'sound_730 v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10
  = du_twoK'45'sound_730 v0 v4 v8 v9
du_twoK'45'sound_730 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
du_twoK'45'sound_730 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           du_map'45'sound_28
                           (coe
                              MAlonzo.Code.Once.Parser.Generic.Parser.du_atomA_470 (coe v0)
                              (coe v7))
                           (coe
                              (\ v9 v10 v11 ->
                                 coe
                                   v2 v7 v10 v5 v9 (coe v3 v5 v7 erased)
                                   (coe du_sound'45'atom_676 (coe v0) (coe v7) (coe v9) (coe v10))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.nuTry-sound
d_nuTry'45'sound_746 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_nuTry'45'sound_746 v0 v1 ~v2 v3 ~v4 ~v5 v6 ~v7
  = du_nuTry'45'sound_746 v0 v1 v3 v6
du_nuTry'45'sound_746 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
du_nuTry'45'sound_746 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'nu_438 v5
                           (coe v3 v5 v7 erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_nuAct'45'sound_758 (coe v0)
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.d_actHead'63'_240 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.nuAct-sound
d_nuAct'45'sound_758 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_nuAct'45'sound_758 v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_nuAct'45'sound_758 v0 v3
du_nuAct'45'sound_758 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
du_nuAct'45'sound_758 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_nuClose'45'sound_556
                    (coe
                       MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumA_612 (coe v0)
                       (coe v3))
                    (\ v5 v6 v7 -> coe du_sound'45'fSum_1082 (coe v0) (coe v3) v5 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-prod
d_sound'45'prod_768 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362
d_sound'45'prod_768 v0 v1 ~v2 v3 v4 ~v5
  = du_sound'45'prod_768 v0 v1 v3 v4
du_sound'45'prod_768 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362
du_sound'45'prod_768 v0 v1 v2 v3
  = coe
      du_prodK'45'sound_784 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Parser.du_atomA_470 (coe v0)
         (coe v1))
      (coe v2) (coe v3)
      (\ v4 v5 v6 -> coe du_sound'45'atom_676 (coe v0) (coe v1) v4 v5)
-- Once.Parser.Generic.Sound.Make.prodK-sound
d_prodK'45'sound_784 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362
d_prodK'45'sound_784 v0 ~v1 v2 ~v3 v4 v5 v6 ~v7
  = du_prodK'45'sound_784 v0 v2 v4 v5 v6
du_prodK'45'sound_784 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362
du_prodK'45'sound_784 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_476 v8 v6
                           (coe v4 v6 v8 erased)
                           (coe
                              du_sound'45'prodTail_796 (coe v0) (coe v6) (coe v8) (coe v2)
                              (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-prodTail
d_sound'45'prodTail_796 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364
d_sound'45'prodTail_796 v0 v1 v2 ~v3 v4 v5 ~v6
  = du_sound'45'prodTail_796 v0 v1 v2 v4 v5
du_sound'45'prodTail_796 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364
du_sound'45'prodTail_796 v0 v1 v2 v3 v4
  = coe
      du_ptGo'45'sound_812 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v2))
      (coe v3) (coe v4)
-- Once.Parser.Generic.Sound.Make.ptGo-sound
d_ptGo'45'sound_812 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364
d_ptGo'45'sound_812 v0 v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 ~v9
  = du_ptGo'45'sound_812 v0 v1 v2 v3 v6 v7
du_ptGo'45'sound_812 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364
du_ptGo'45'sound_812 v0 v1 v2 v3 v4 v5
  = if coe v3
      then coe
             du_ptK'45'sound_832 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_atomA_470 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
             (coe v4) (coe v5)
             (\ v6 v7 v8 ->
                coe
                  du_sound'45'atom_676 (coe v0)
                  (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2))
                  v6 v7)
      else coe
             MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'done_482
-- Once.Parser.Generic.Sound.Make.ptK-sound
d_ptK'45'sound_832 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364
d_ptK'45'sound_832 v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_ptK'45'sound_832 v0 v1 v4 v6 v7 v9
du_ptK'45'sound_832 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364
du_ptK'45'sound_832 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_ppt'45'star_496 v9 v7
                           (coe v5 v7 v9 erased)
                           (coe
                              du_sound'45'prodTail_796 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Parser.Generic.Relation.d_aProd_160 v0 v1 v7)
                              (coe v9) (coe v3) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-sum
d_sound'45'sum_842 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366
d_sound'45'sum_842 v0 v1 ~v2 v3 v4 ~v5
  = du_sound'45'sum_842 v0 v1 v3 v4
du_sound'45'sum_842 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366
du_sound'45'sum_842 v0 v1 v2 v3
  = coe
      du_sumK'45'sound_858 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Parser.du_prodA_512 (coe v0)
         (coe v1))
      (coe v2) (coe v3)
      (\ v4 v5 v6 -> coe du_sound'45'prod_768 (coe v0) (coe v1) v4 v5)
-- Once.Parser.Generic.Sound.Make.sumK-sound
d_sumK'45'sound_858 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366
d_sumK'45'sound_858 v0 ~v1 v2 ~v3 v4 v5 v6 ~v7
  = du_sumK'45'sound_858 v0 v2 v4 v5 v6
du_sumK'45'sound_858 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366
du_sumK'45'sound_858 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_508 v8 v6
                           (coe v4 v6 v8 erased)
                           (coe
                              du_sound'45'sumTail_870 (coe v0) (coe v6) (coe v8) (coe v2)
                              (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-sumTail
d_sound'45'sumTail_870 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368
d_sound'45'sumTail_870 v0 v1 v2 ~v3 v4 v5 ~v6
  = du_sound'45'sumTail_870 v0 v1 v2 v4 v5
du_sound'45'sumTail_870 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368
du_sound'45'sumTail_870 v0 v1 v2 v3 v4
  = coe
      du_stGo'45'sound_886 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v2))
      (coe v3) (coe v4)
-- Once.Parser.Generic.Sound.Make.stGo-sound
d_stGo'45'sound_886 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368
d_stGo'45'sound_886 v0 v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 ~v9
  = du_stGo'45'sound_886 v0 v1 v2 v3 v6 v7
du_stGo'45'sound_886 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368
du_stGo'45'sound_886 v0 v1 v2 v3 v4 v5
  = if coe v3
      then coe
             du_stK'45'sound_906 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_prodA_512 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
             (coe v4) (coe v5)
             (\ v6 v7 v8 ->
                coe
                  du_sound'45'prod_768 (coe v0)
                  (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2))
                  v6 v7)
      else coe
             MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'done_514
-- Once.Parser.Generic.Sound.Make.stK-sound
d_stK'45'sound_906 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368
d_stK'45'sound_906 v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_stK'45'sound_906 v0 v1 v4 v6 v7 v9
du_stK'45'sound_906 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368
du_stK'45'sound_906 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pst'45'plus_528 v9 v7
                           (coe v5 v7 v9 erased)
                           (coe
                              du_sound'45'sumTail_870 (coe v0)
                              (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_aSum_162 v0 v1 v7)
                              (coe v9) (coe v3) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-type
d_sound'45'type_916 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370
d_sound'45'type_916 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'type_916 v0 v1
du_sound'45'type_916 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370
du_sound'45'type_916 v0 v1
  = coe
      du_typeK'45'sound_932 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Parser.du_sumA_534 (coe v0)
         (coe v1))
      (\ v2 v3 v4 -> coe du_sound'45'sum_842 (coe v0) (coe v1) v2 v3)
-- Once.Parser.Generic.Sound.Make.typeK-sound
d_typeK'45'sound_932 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370
d_typeK'45'sound_932 v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_typeK'45'sound_932 v0 v2 v6
du_typeK'45'sound_932 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370
du_typeK'45'sound_932 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_540 v6 v4
                           (coe v2 v4 v6 erased)
                           (coe du_sound'45'arrowTail_944 (coe v0) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-arrowTail
d_sound'45'arrowTail_944 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372
d_sound'45'arrowTail_944 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'arrowTail_944 v0 v2
du_sound'45'arrowTail_944 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372
du_sound'45'arrowTail_944 v0 v1
  = coe
      du_atGo'45'sound_962 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Relation.d_arrowDir_22 (coe v1))
-- Once.Parser.Generic.Sound.Make.atGo-sound
d_atGo'45'sound_962 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372
d_atGo'45'sound_962 v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_atGo'45'sound_962 v0 v2 v3
du_atGo'45'sound_962 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372
du_atGo'45'sound_962 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adG_14 v3
        -> coe
             du_arrK'45'sound_630
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_typeA_556 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34 (coe v1)))
             (coe
                (\ v4 v5 v6 ->
                   coe
                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow'45'g_558
                     v4 v3
                     (coe
                        du_sound'45'type_916 (coe v0)
                        (coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34 (coe v1)))))
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adA_16
        -> coe
             du_arrK'45'sound_630
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_typeA_556 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)))
             (coe
                (\ v3 v4 v5 ->
                   coe
                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'arrow_568 v3
                     (coe
                        du_sound'45'type_916 (coe v0)
                        (coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v1)))))
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adD_20
        -> coe MAlonzo.Code.Once.Parser.Generic.Relation.C_pat'45'done_546
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-fAtom
d_sound'45'fAtom_972 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374
d_sound'45'fAtom_972 v0 v1 ~v2 ~v3 v4 ~v5
  = du_sound'45'fAtom_972 v0 v1 v4
du_sound'45'fAtom_972 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374
du_sound'45'fAtom_972 v0 v1 v2
  = coe
      du_fAtomH'45'sound_984 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Parser.Generic.Parser.d_headV_264 (coe v1))
      (coe v2)
-- Once.Parser.Generic.Sound.Make.fAtomH-sound
d_fAtomH'45'sound_984 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_HeadV_246 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374
d_fAtomH'45'sound_984 v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_fAtomH'45'sound_984 v0 v1 v2 v5
du_fAtomH'45'sound_984 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_HeadV_246 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374
du_fAtomH'45'sound_984 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Generic.Parser.C_hWord_252
        -> case coe v1 of
             (:) v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Parser.Token.C_TWord_8 v8
                      -> coe
                           du_fkwK'45'sound_998 (coe v0) (coe v7)
                           (coe MAlonzo.Code.Once.Parser.Generic.Parser.d_fkwV_218 (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Parser.Generic.Parser.C_hParen_256
        -> case coe v1 of
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'paren_590
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v3))
                    (coe
                       du_parenK'45'sound_488
                       (coe
                          MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumA_612 (coe v0)
                          (coe v6))
                       (\ v7 v8 v9 -> coe du_sound'45'fSum_1082 (coe v0) (coe v6) v7 v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.fkwK-sound
d_fkwK'45'sound_998 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_FKwV_186 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374
d_fkwK'45'sound_998 v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_fkwK'45'sound_998 v0 v2 v3
du_fkwK'45'sound_998 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_FKwV_186 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374
du_fkwK'45'sound_998 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Generic.Parser.C_fvId_188
        -> coe MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'id_572
      MAlonzo.Code.Once.Parser.Generic.Parser.C_fvK_190
        -> coe
             du_map'45'sound_28
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_atomA_470 (coe v0)
                (coe v1))
             (coe
                (\ v3 v4 v5 ->
                   coe
                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pfa'45'k_580 v3
                     (coe du_sound'45'atom_676 (coe v0) (coe v1) (coe v3) (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-fProd
d_sound'45'fProd_1008 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376
d_sound'45'fProd_1008 v0 v1 ~v2 v3 v4 ~v5
  = du_sound'45'fProd_1008 v0 v1 v3 v4
du_sound'45'fProd_1008 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376
du_sound'45'fProd_1008 v0 v1 v2 v3
  = coe
      du_fProdK'45'sound_1024 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Parser.du_fAtomA_576 (coe v0)
         (coe v1))
      (coe v2) (coe v3)
      (\ v4 v5 v6 -> coe du_sound'45'fAtom_972 (coe v0) (coe v1) v5)
-- Once.Parser.Generic.Sound.Make.fProdK-sound
d_fProdK'45'sound_1024 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376
d_fProdK'45'sound_1024 v0 ~v1 v2 ~v3 v4 v5 v6 ~v7
  = du_fProdK'45'sound_1024 v0 v2 v4 v5 v6
du_fProdK'45'sound_1024 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376
du_fProdK'45'sound_1024 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfp'45'mk_602 v8 v6
                           (coe v4 v6 v8 erased)
                           (coe
                              du_sound'45'fProdTail_1036 (coe v0) (coe v6) (coe v8) (coe v2)
                              (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-fProdTail
d_sound'45'fProdTail_1036 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378
d_sound'45'fProdTail_1036 v0 v1 v2 ~v3 v4 v5 ~v6
  = du_sound'45'fProdTail_1036 v0 v1 v2 v4 v5
du_sound'45'fProdTail_1036 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378
du_sound'45'fProdTail_1036 v0 v1 v2 v3 v4
  = coe
      du_fptGo'45'sound_1052 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v2))
      (coe v3) (coe v4)
-- Once.Parser.Generic.Sound.Make.fptGo-sound
d_fptGo'45'sound_1052 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378
d_fptGo'45'sound_1052 v0 v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 ~v9
  = du_fptGo'45'sound_1052 v0 v1 v2 v3 v6 v7
du_fptGo'45'sound_1052 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378
du_fptGo'45'sound_1052 v0 v1 v2 v3 v4 v5
  = if coe v3
      then coe
             du_fptK'45'sound_1072 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_fAtomA_576 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
             (coe v4) (coe v5)
             (\ v6 v7 v8 ->
                coe
                  du_sound'45'fAtom_972 (coe v0)
                  (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2))
                  v7)
      else coe
             MAlonzo.Code.Once.Parser.Generic.Relation.C_pfpt'45'done_608
-- Once.Parser.Generic.Sound.Make.fptK-sound
d_fptK'45'sound_1072 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378
d_fptK'45'sound_1072 v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_fptK'45'sound_1072 v0 v1 v4 v6 v7 v9
du_fptK'45'sound_1072 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378
du_fptK'45'sound_1072 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfpt'45'star_622 v9 v7
                           (coe v5 v7 v9 erased)
                           (coe
                              du_sound'45'fProdTail_1036 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Parser.Generic.Relation.d_fProd_182 v0 v1 v7)
                              (coe v9) (coe v3) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-fSum
d_sound'45'fSum_1082 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380
d_sound'45'fSum_1082 v0 v1 ~v2 v3 v4 ~v5
  = du_sound'45'fSum_1082 v0 v1 v3 v4
du_sound'45'fSum_1082 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380
du_sound'45'fSum_1082 v0 v1 v2 v3
  = coe
      du_fSumK'45'sound_1098 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdA_590 (coe v0)
         (coe v1))
      (coe v2) (coe v3)
      (\ v4 v5 v6 -> coe du_sound'45'fProd_1008 (coe v0) (coe v1) v4 v5)
-- Once.Parser.Generic.Sound.Make.fSumK-sound
d_fSumK'45'sound_1098 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380
d_fSumK'45'sound_1098 v0 ~v1 v2 ~v3 v4 v5 v6 ~v7
  = du_fSumK'45'sound_1098 v0 v2 v4 v5 v6
du_fSumK'45'sound_1098 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380
du_fSumK'45'sound_1098 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfs'45'mk_634 v8 v6
                           (coe v4 v6 v8 erased)
                           (coe
                              du_sound'45'fSumTail_1110 (coe v0) (coe v6) (coe v8) (coe v2)
                              (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-fSumTail
d_sound'45'fSumTail_1110 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382
d_sound'45'fSumTail_1110 v0 v1 v2 ~v3 v4 v5 ~v6
  = du_sound'45'fSumTail_1110 v0 v1 v2 v4 v5
du_sound'45'fSumTail_1110 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382
du_sound'45'fSumTail_1110 v0 v1 v2 v3 v4
  = coe
      du_fstGo'45'sound_1126 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v2))
      (coe v3) (coe v4)
-- Once.Parser.Generic.Sound.Make.fstGo-sound
d_fstGo'45'sound_1126 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382
d_fstGo'45'sound_1126 v0 v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 ~v9
  = du_fstGo'45'sound_1126 v0 v1 v2 v3 v6 v7
du_fstGo'45'sound_1126 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382
du_fstGo'45'sound_1126 v0 v1 v2 v3 v4 v5
  = if coe v3
      then coe
             du_fstK'45'sound_1146 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdA_590 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
             (coe v4) (coe v5)
             (\ v6 v7 v8 ->
                coe
                  du_sound'45'fProd_1008 (coe v0)
                  (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2))
                  v6 v7)
      else coe
             MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'done_640
-- Once.Parser.Generic.Sound.Make.fstK-sound
d_fstK'45'sound_1146 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382
d_fstK'45'sound_1146 v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_fstK'45'sound_1146 v0 v1 v4 v6 v7 v9
du_fstK'45'sound_1146 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376) ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382
du_fstK'45'sound_1146 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pfst'45'plus_654 v9 v7
                           (coe v5 v7 v9 erased)
                           (coe
                              du_sound'45'fSumTail_1110 (coe v0)
                              (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_fSum_180 v0 v1 v7)
                              (coe v9) (coe v3) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Sound.Make.sound-atomP
d_sound'45'atomP_1776 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_sound'45'atomP_1776 v0 v1 v2 v3 v4
  = coe du_sound'45'atom_676 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Parser.Generic.Sound.Make.sound-typeP
d_sound'45'typeP_1786 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370
d_sound'45'typeP_1786 v0 v1 ~v2 ~v3 = du_sound'45'typeP_1786 v0 v1
du_sound'45'typeP_1786 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370
du_sound'45'typeP_1786 v0 v1 v2
  = coe du_sound'45'type_916 (coe v0) (coe v1)
-- Once.Parser.Generic.Sound.Make.sound-fSumP
d_sound'45'fSumP_1796 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380
d_sound'45'fSumP_1796 v0 v1 v2 v3 v4
  = coe du_sound'45'fSum_1082 (coe v0) (coe v1) (coe v2) (coe v3)
