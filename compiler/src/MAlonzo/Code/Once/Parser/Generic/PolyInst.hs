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
                (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe v0))
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
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
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
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_TVarRel_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tvar'45'complete_110 = erased
-- Once.Parser.Generic.PolyInst.PolyAlg
d_PolyAlg_118 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46
d_PolyAlg_118
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.C_constructor_244
      (coe MAlonzo.Code.Once.Type.C_PUnit_264)
      (coe MAlonzo.Code.Once.Type.C_PVoid_266)
      (coe MAlonzo.Code.Once.Type.C_PInt_280)
      (coe MAlonzo.Code.Once.Type.C_PFloat_282)
      (coe MAlonzo.Code.Once.Type.C__P'42'__268)
      (coe MAlonzo.Code.Once.Type.C__P'43'__270)
      (coe MAlonzo.Code.Once.Type.C_PEff_274)
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 (coe v1) (coe v0))
      (coe MAlonzo.Code.Once.Type.C_Pμ'45'type_276)
      (\ v0 ->
         coe
           MAlonzo.Code.Once.Type.C_Pν'45'type_278 (coe v0)
           (coe MAlonzo.Code.Once.Type.C_pure_34))
      (\ v0 ->
         coe
           MAlonzo.Code.Once.Type.C_Pν'45'type_278 (coe v0)
           (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Type.C_PK_256)
      (coe MAlonzo.Code.Once.Type.C_PId_258)
      (coe MAlonzo.Code.Once.Type.C__P'8853'__260)
      (coe MAlonzo.Code.Once.Type.C__P'8855'__262)
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
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_364 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_typeShrink_166 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_typeShrink_706
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
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_366 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowTailShrink_176 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_arrowTailShrink_698
      (coe d_PolyAlg_118) v1 v3 v4
-- Once.Parser.Generic.PolyInst._.atomShrink
d_atomShrink_178 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_354 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_atomShrink_178
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.d_atomShrink_652
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.funcAtomShrink
d_funcAtomShrink_180 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcAtomShrink_180
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.d_funcAtomShrink_714
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.funcProdShrink
d_funcProdShrink_182 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_370 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdShrink_182 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcProdShrink_722
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.funcProdTailShrink
d_funcProdTailShrink_184 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_372 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdTailShrink_184 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcProdTailShrink_732
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.funcSumShrink
d_funcSumShrink_186 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_374 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumShrink_186 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcSumShrink_740
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.funcSumTailShrink
d_funcSumTailShrink_188 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_376 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumTailShrink_188 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcSumTailShrink_750
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.prodShrink
d_prodShrink_242 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_356 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodShrink_242 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_prodShrink_660
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.prodTailShrink
d_prodTailShrink_244 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_358 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodTailShrink_244 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_prodTailShrink_670
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.sumShrink
d_sumShrink_254 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_360 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumShrink_254 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_sumShrink_678
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.sumTailShrink
d_sumTailShrink_256 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_362 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumTailShrink_256 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_sumTailShrink_688
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.arrowTailP
d_arrowTailP_344 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_344
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_108
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.atomKw
d_atomKw_346 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_346
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_120
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.atomP
d_atomP_348 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_348
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_96
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fAtomP
d_fAtomP_350 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_350
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_110
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fProdP
d_fProdP_352 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_352
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_112
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fProdTailP
d_fProdTailP_354 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_354
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_116
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fSumP
d_fSumP_356 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_356
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_114
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fSumTailP
d_fSumTailP_358 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_358
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_118
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuCloseP
d_nuCloseP_360 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuCloseP_360
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuCloseP_128
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuEffP
d_nuEffP_362 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuEffP_362
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuEffP_124
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuEffWith
d_nuEffWith_364 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuEffWith_364 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuEffWith_134
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.nuP
d_nuP_366 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuP_366
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuP_122
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuTryP
d_nuTryP_368 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuTryP_368
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuTryP_126
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.typeP
d_typeP_370 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_370
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_102
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.prodP
d_prodP_372 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_372
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_98
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.prodTailP
d_prodTailP_374 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_374
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_104
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sumP
d_sumP_376 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_376
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_100
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sumTailP
d_sumTailP_378 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_378
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_106
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sound-arrowTail
d_sound'45'arrowTail_382 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_366
d_sound'45'arrowTail_382 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_404
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-atom
d_sound'45'atom_384 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_354
d_sound'45'atom_384 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'atom_314
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fAtom
d_sound'45'fAtom_386 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_368
d_sound'45'fAtom_386 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fAtom_414
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fProd
d_sound'45'fProd_388 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_370
d_sound'45'fProd_388 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProd_424
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fProdTail
d_sound'45'fProdTail_390 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_372
d_sound'45'fProdTail_390 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProdTail_436
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-fSum
d_sound'45'fSum_392 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_374
d_sound'45'fSum_392 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSum_446
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fSumTail
d_sound'45'fSumTail_394 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_376
d_sound'45'fSumTail_394 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSumTail_458
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-kw
d_sound'45'kw_396 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_354
d_sound'45'kw_396 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_338
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-nuEff
d_sound'45'nuEff_398 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_354
d_sound'45'nuEff_398 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'nuEff_328
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-type
d_sound'45'type_400 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_364
d_sound'45'type_400 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'type_392
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-prod
d_sound'45'prod_402 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_356
d_sound'45'prod_402 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prod_348
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-prodTail
d_sound'45'prodTail_404 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_358
d_sound'45'prodTail_404 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_360
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-sum
d_sound'45'sum_406 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_360
d_sound'45'sum_406 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sum_370
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-sumTail
d_sound'45'sumTail_408 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_362
d_sound'45'sumTail_408 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_382
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.complete-arrowTail
d_complete'45'arrowTail_412 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_412 = erased
-- Once.Parser.Generic.PolyInst._.complete-atom
d_complete'45'atom_414 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_354 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_414 = erased
-- Once.Parser.Generic.PolyInst._.complete-fAtom
d_complete'45'fAtom_416 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_416 = erased
-- Once.Parser.Generic.PolyInst._.complete-fProd
d_complete'45'fProd_418 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_370 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_418 = erased
-- Once.Parser.Generic.PolyInst._.complete-fProdTail
d_complete'45'fProdTail_420 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_372 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_420 = erased
-- Once.Parser.Generic.PolyInst._.complete-fSum
d_complete'45'fSum_422 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_422 = erased
-- Once.Parser.Generic.PolyInst._.complete-fSumTail
d_complete'45'fSumTail_424 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_424 = erased
-- Once.Parser.Generic.PolyInst._.complete-type
d_complete'45'type_426 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_426 = erased
-- Once.Parser.Generic.PolyInst._.complete-prod
d_complete'45'prod_428 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_356 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_428 = erased
-- Once.Parser.Generic.PolyInst._.complete-prodTail
d_complete'45'prodTail_430 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_430 = erased
-- Once.Parser.Generic.PolyInst._.complete-sum
d_complete'45'sum_432 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_432 = erased
-- Once.Parser.Generic.PolyInst._.complete-sumTail
d_complete'45'sumTail_434 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_362 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_434 = erased
-- Once.Parser.Generic.PolyInst._.fSum-parenEff
d_fSum'45'parenEff_436 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenEff_436 = erased
