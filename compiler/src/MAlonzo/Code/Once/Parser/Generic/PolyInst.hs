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
      MAlonzo.Code.Once.Parser.Generic.Relation.C_constructor_264
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
      (coe MAlonzo.Code.Once.Type.C_Pν'45'type_264)
      (coe MAlonzo.Code.Once.Type.C_PK_242)
      (coe MAlonzo.Code.Once.Type.C_PId_244)
      (coe MAlonzo.Code.Once.Type.C__P'8853'__246)
      (coe MAlonzo.Code.Once.Type.C__P'8855'__248)
      (\ v0 v1 v2 v3 -> coe du_tvar'45'shrink_58 v2 v3) d_tvarP_46
-- Once.Parser.Generic.PolyInst._.ParsesArrowTailG
d_ParsesArrowTailG_150 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesAtomG
d_ParsesAtomG_152 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncAtomG
d_ParsesFuncAtomG_154 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncProdG
d_ParsesFuncProdG_156 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_158 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncSumG
d_ParsesFuncSumG_160 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_162 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesTypeG
d_ParsesTypeG_164 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.typeShrink
d_typeShrink_166 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_390 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_typeShrink_166 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_typeShrink_732
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst._.ParsesProdG
d_ParsesProdG_168 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesProdTailG
d_ParsesProdTailG_170 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesSumG
d_ParsesSumG_172 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesSumTailG
d_ParsesSumTailG_174 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.arrowTailShrink
d_arrowTailShrink_176 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_392 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowTailShrink_176 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_arrowTailShrink_724
      (coe d_PolyAlg_118) v1 v3 v4
-- Once.Parser.Generic.PolyInst._.atomShrink
d_atomShrink_178 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_380 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_atomShrink_178
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.d_atomShrink_678
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.funcAtomShrink
d_funcAtomShrink_180 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_394 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcAtomShrink_180
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.d_funcAtomShrink_740
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.funcProdShrink
d_funcProdShrink_182 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_396 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdShrink_182 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcProdShrink_748
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.funcProdTailShrink
d_funcProdTailShrink_184 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_398 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdTailShrink_184 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcProdTailShrink_758
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.funcSumShrink
d_funcSumShrink_186 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_400 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumShrink_186 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcSumShrink_766
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.funcSumTailShrink
d_funcSumTailShrink_188 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumTailShrink_188 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcSumTailShrink_776
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.prodShrink
d_prodShrink_244 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_382 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodShrink_244 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_prodShrink_686
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.prodTailShrink
d_prodTailShrink_246 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_384 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodTailShrink_246 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_prodTailShrink_696
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.sumShrink
d_sumShrink_256 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_386 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumShrink_256 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_sumShrink_704
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.sumTailShrink
d_sumTailShrink_258 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_388 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumTailShrink_258 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_sumTailShrink_714
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.arrowTailP
d_arrowTailP_348 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_348
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_92
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.atomKw
d_atomKw_350 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_350
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_104
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.atomP
d_atomP_352 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_352
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_80
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fAtomP
d_fAtomP_354 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_354
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_94
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fProdP
d_fProdP_356 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_356
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_96
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fProdTailP
d_fProdTailP_358 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_358
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_100
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fSumP
d_fSumP_360 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_360
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_98
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fSumTailP
d_fSumTailP_362 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_362
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_102
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.typeP
d_typeP_364 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_364
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_86
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.prodP
d_prodP_366 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_366
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_82
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.prodTailP
d_prodTailP_368 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_368
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_88
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sumP
d_sumP_370 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_370
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_84
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sumTailP
d_sumTailP_372 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_372
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_90
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sound-arrowTail
d_sound'45'arrowTail_376 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_392
d_sound'45'arrowTail_376 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_390
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-atom
d_sound'45'atom_378 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_380
d_sound'45'atom_378 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'atom_314
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fAtom
d_sound'45'fAtom_380 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_394
d_sound'45'fAtom_380 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fAtom_400
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fProd
d_sound'45'fProd_382 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_396
d_sound'45'fProd_382 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProd_410
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fProdTail
d_sound'45'fProdTail_384 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_398
d_sound'45'fProdTail_384 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProdTail_422
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-fSum
d_sound'45'fSum_386 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_400
d_sound'45'fSum_386 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSum_432
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fSumTail
d_sound'45'fSumTail_388 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_402
d_sound'45'fSumTail_388 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSumTail_444
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-kw
d_sound'45'kw_390 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_380
d_sound'45'kw_390 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_324
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-type
d_sound'45'type_392 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_390
d_sound'45'type_392 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'type_378
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-prod
d_sound'45'prod_394 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_382
d_sound'45'prod_394 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prod_334
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-prodTail
d_sound'45'prodTail_396 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_384
d_sound'45'prodTail_396 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_346
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-sum
d_sound'45'sum_398 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_386
d_sound'45'sum_398 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sum_356
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-sumTail
d_sound'45'sumTail_400 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_388
d_sound'45'sumTail_400 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_368
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.complete-arrowTail
d_complete'45'arrowTail_404 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_392 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_404 = erased
-- Once.Parser.Generic.PolyInst._.complete-atom
d_complete'45'atom_406 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_406 = erased
-- Once.Parser.Generic.PolyInst._.complete-fAtom
d_complete'45'fAtom_408 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_408 = erased
-- Once.Parser.Generic.PolyInst._.complete-fProd
d_complete'45'fProd_410 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_410 = erased
-- Once.Parser.Generic.PolyInst._.complete-fProdTail
d_complete'45'fProdTail_412 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_398 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_412 = erased
-- Once.Parser.Generic.PolyInst._.complete-fSum
d_complete'45'fSum_414 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_400 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_414 = erased
-- Once.Parser.Generic.PolyInst._.complete-fSumTail
d_complete'45'fSumTail_416 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_416 = erased
-- Once.Parser.Generic.PolyInst._.complete-type
d_complete'45'type_418 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_390 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_418 = erased
-- Once.Parser.Generic.PolyInst._.complete-prod
d_complete'45'prod_420 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_420 = erased
-- Once.Parser.Generic.PolyInst._.complete-prodTail
d_complete'45'prodTail_422 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_422 = erased
-- Once.Parser.Generic.PolyInst._.complete-sum
d_complete'45'sum_424 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_424 = erased
-- Once.Parser.Generic.PolyInst._.complete-sumTail
d_complete'45'sumTail_426 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_388 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_426 = erased
