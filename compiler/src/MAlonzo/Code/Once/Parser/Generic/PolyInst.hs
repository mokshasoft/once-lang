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

module MAlonzo.Code.Once.Parser.Generic.PolyInst where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.CharClass
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Generic.Sound
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type

-- Once.Parser.Generic.PolyInst.TVarRel
d_TVarRel_8 a0 a1 a2 = ()
data T_TVarRel_8 = C_tvar_14
-- Once.Parser.Generic.PolyInst.tvarGo
d_tvarGo_26 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tvarGo_26 v0 v1 v2 ~v3 = du_tvarGo_26 v0 v1 v2
du_tvarGo_26 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tvarGo_26 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Once.Type.C_PTVar_274 (coe v0))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe C_tvar_14)))
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Parser.Generic.PolyInst.tvarP
d_tvarP_46 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tvarP_46 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
                  -> coe
                       du_tvarGo_26 (coe v4) (coe v2)
                       (coe MAlonzo.Code.Once.Parser.CharClass.d_isLowerWord_6 (coe v4))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.PolyInst.tvar-shrink
d_tvar'45'shrink_58 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_TVarRel_8 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tvar'45'shrink_58 ~v0 ~v1 v2 v3 = du_tvar'45'shrink_58 v2 v3
du_tvar'45'shrink_58 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_TVarRel_8 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tvar'45'shrink_58 v0 v1
  = coe
      seq (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
            (coe
               MAlonzo.Code.Data.List.Base.du_foldr_216
               (let v2 = \ v2 -> addInt (coe (1 :: Integer)) (coe v2) in
                coe (coe (\ v3 -> v2)))
               (coe (0 :: Integer)) (coe v0))))
-- Once.Parser.Generic.PolyInst.tvarGo-complete
d_tvarGo'45'complete_70 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tvarGo'45'complete_70 = erased
-- Once.Parser.Generic.PolyInst.tvar-complete
d_tvar'45'complete_110 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_TVarRel_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tvar'45'complete_110 = erased
-- Once.Parser.Generic.PolyInst.PolyAlg
d_PolyAlg_118 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46
d_PolyAlg_118
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.C_constructor_252
      (coe MAlonzo.Code.Once.Type.C_PUnit_250)
      (coe MAlonzo.Code.Once.Type.C_PVoid_252)
      (coe MAlonzo.Code.Once.Type.C_PInt_266)
      (coe MAlonzo.Code.Once.Type.C_PFloat_268)
      (coe MAlonzo.Code.Once.Type.C_PBuffer_272)
      (coe MAlonzo.Code.Once.Type.C_PStr_270)
      (coe MAlonzo.Code.Once.Type.C__P'42'__254)
      (coe MAlonzo.Code.Once.Type.C__P'43'__256)
      (coe MAlonzo.Code.Once.Type.C_PEff_260)
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258 (coe v1) (coe v0))
      (coe MAlonzo.Code.Once.Type.C_Pμ'45'type_262)
      (coe MAlonzo.Code.Once.Type.C_PK_242)
      (coe MAlonzo.Code.Once.Type.C_PId_244)
      (coe MAlonzo.Code.Once.Type.C__P'8853'__246)
      (coe MAlonzo.Code.Once.Type.C__P'8855'__248)
      (\ v0 v1 v2 v3 -> coe du_tvar'45'shrink_58 v2 v3) d_tvarP_46
-- Once.Parser.Generic.PolyInst._.ParsesArrowTailG
d_ParsesArrowTailG_148 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesAtomG
d_ParsesAtomG_150 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncAtomG
d_ParsesFuncAtomG_152 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncProdG
d_ParsesFuncProdG_154 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_156 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncSumG
d_ParsesFuncSumG_158 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_160 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesTypeG
d_ParsesTypeG_162 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.typeShrink
d_typeShrink_164 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_typeShrink_164 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_typeShrink_708
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst._.ParsesProdG
d_ParsesProdG_166 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesProdTailG
d_ParsesProdTailG_168 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesSumG
d_ParsesSumG_170 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesSumTailG
d_ParsesSumTailG_172 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.arrowTailShrink
d_arrowTailShrink_174 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_376 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowTailShrink_174 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_arrowTailShrink_700
      (coe d_PolyAlg_118) v1 v3 v4
-- Once.Parser.Generic.PolyInst._.atomShrink
d_atomShrink_176 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_364 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_atomShrink_176
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.d_atomShrink_654
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.funcAtomShrink
d_funcAtomShrink_178 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_378 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcAtomShrink_178
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.d_funcAtomShrink_716
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.funcProdShrink
d_funcProdShrink_180 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_380 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdShrink_180 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcProdShrink_724
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.funcProdTailShrink
d_funcProdTailShrink_182 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_382 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdTailShrink_182 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcProdTailShrink_734
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.funcSumShrink
d_funcSumShrink_184 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_384 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumShrink_184 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcSumShrink_742
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.funcSumTailShrink
d_funcSumTailShrink_186 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_386 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumTailShrink_186 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcSumTailShrink_752
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.prodShrink
d_prodShrink_240 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_366 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodShrink_240 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_prodShrink_662
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.prodTailShrink
d_prodTailShrink_242 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodTailShrink_242 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_prodTailShrink_672
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.sumShrink
d_sumShrink_252 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_370 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumShrink_252 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_sumShrink_680
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.sumTailShrink
d_sumTailShrink_254 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_372 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumTailShrink_254 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_sumTailShrink_690
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.arrowTailP
d_arrowTailP_342 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_342
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_88
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.atomKw
d_atomKw_344 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_344
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.atomP
d_atomP_346 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_346
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_76
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fAtomP
d_fAtomP_348 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_348
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_90
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fProdP
d_fProdP_350 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_350
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_92
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fProdTailP
d_fProdTailP_352 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_352
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_96
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fSumP
d_fSumP_354 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_354
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_94
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fSumTailP
d_fSumTailP_356 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_356
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_98
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.typeP
d_typeP_358 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_358
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_82
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.prodP
d_prodP_360 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_360
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_78
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.prodTailP
d_prodTailP_362 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_362
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sumP
d_sumP_364 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_364
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_80
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sumTailP
d_sumTailP_366 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_366
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sound-arrowTail
d_sound'45'arrowTail_370 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_376
d_sound'45'arrowTail_370 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_382
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-atom
d_sound'45'atom_372 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_364
d_sound'45'atom_372 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'atom_306
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fAtom
d_sound'45'fAtom_374 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_378
d_sound'45'fAtom_374 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fAtom_392
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fProd
d_sound'45'fProd_376 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_380
d_sound'45'fProd_376 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProd_402
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fProdTail
d_sound'45'fProdTail_378 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_382
d_sound'45'fProdTail_378 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProdTail_414
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-fSum
d_sound'45'fSum_380 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_384
d_sound'45'fSum_380 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSum_424
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fSumTail
d_sound'45'fSumTail_382 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_386
d_sound'45'fSumTail_382 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSumTail_436
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-kw
d_sound'45'kw_384 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_364
d_sound'45'kw_384 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_316
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-type
d_sound'45'type_386 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374
d_sound'45'type_386 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'type_370
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-prod
d_sound'45'prod_388 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_366
d_sound'45'prod_388 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prod_326
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-prodTail
d_sound'45'prodTail_390 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_368
d_sound'45'prodTail_390 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-sum
d_sound'45'sum_392 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_370
d_sound'45'sum_392 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sum_348
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-sumTail
d_sound'45'sumTail_394 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_372
d_sound'45'sumTail_394 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.complete-arrowTail
d_complete'45'arrowTail_398 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_398 = erased
-- Once.Parser.Generic.PolyInst._.complete-atom
d_complete'45'atom_400 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_400 = erased
-- Once.Parser.Generic.PolyInst._.complete-fAtom
d_complete'45'fAtom_402 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_402 = erased
-- Once.Parser.Generic.PolyInst._.complete-fProd
d_complete'45'fProd_404 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_404 = erased
-- Once.Parser.Generic.PolyInst._.complete-fProdTail
d_complete'45'fProdTail_406 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_406 = erased
-- Once.Parser.Generic.PolyInst._.complete-fSum
d_complete'45'fSum_408 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_408 = erased
-- Once.Parser.Generic.PolyInst._.complete-fSumTail
d_complete'45'fSumTail_410 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_410 = erased
-- Once.Parser.Generic.PolyInst._.complete-type
d_complete'45'type_412 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_412 = erased
-- Once.Parser.Generic.PolyInst._.complete-prod
d_complete'45'prod_414 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_414 = erased
-- Once.Parser.Generic.PolyInst._.complete-prodTail
d_complete'45'prodTail_416 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_416 = erased
-- Once.Parser.Generic.PolyInst._.complete-sum
d_complete'45'sum_418 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_370 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_418 = erased
-- Once.Parser.Generic.PolyInst._.complete-sumTail
d_complete'45'sumTail_420 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_372 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_420 = erased
