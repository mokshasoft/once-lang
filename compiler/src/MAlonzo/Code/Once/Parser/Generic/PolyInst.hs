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
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Parser.CharClass
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Generic.Sound
import qualified MAlonzo.Code.Once.Parser.Token

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
                (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe v0))
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
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
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
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_TVarRel_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tvar'45'complete_110 = erased
-- Once.Parser.Generic.PolyInst.PolyAlg
d_PolyAlg_118 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46
d_PolyAlg_118
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.C_constructor_260
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20)
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PVoid_22)
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38)
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PFloat_40)
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24)
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26)
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30)
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32)
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 (coe v1)
           (coe v0))
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34)
      (\ v0 ->
         coe
           MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 (coe v0)
           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
      (\ v0 ->
         coe
           MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 (coe v0)
           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40))
      (\ v0 ->
         coe
           MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 (coe v0)
           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12)
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14)
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16)
      (coe MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18)
      (\ v0 v1 v2 v3 -> coe du_tvar'45'shrink_58 v2 v3) d_tvarP_46
-- Once.Parser.Generic.PolyInst._.ParsesArrowTailG
d_ParsesArrowTailG_154 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesAtomG
d_ParsesAtomG_156 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncAtomG
d_ParsesFuncAtomG_158 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncProdG
d_ParsesFuncProdG_160 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_162 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncSumG
d_ParsesFuncSumG_164 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_166 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesTypeG
d_ParsesTypeG_168 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.typeShrink
d_typeShrink_170 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_386 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_typeShrink_170 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_typeShrink_748
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst._.ParsesProdG
d_ParsesProdG_172 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesProdTailG
d_ParsesProdTailG_174 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesSumG
d_ParsesSumG_176 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesSumTailG
d_ParsesSumTailG_178 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.arrowTailShrink
d_arrowTailShrink_180 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_388 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowTailShrink_180 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_arrowTailShrink_740
      (coe d_PolyAlg_118) v1 v3 v4
-- Once.Parser.Generic.PolyInst._.atomShrink
d_atomShrink_182 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_atomShrink_182
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.d_atomShrink_694
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.funcAtomShrink
d_funcAtomShrink_184 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_390 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcAtomShrink_184
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.d_funcAtomShrink_756
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.funcProdShrink
d_funcProdShrink_186 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_392 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdShrink_186 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcProdShrink_764
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.funcProdTailShrink
d_funcProdTailShrink_188 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_394 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdTailShrink_188 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcProdTailShrink_774
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.funcSumShrink
d_funcSumShrink_190 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_396 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumShrink_190 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcSumShrink_782
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.funcSumTailShrink
d_funcSumTailShrink_192 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_398 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumTailShrink_192 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcSumTailShrink_792
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.prodShrink
d_prodShrink_250 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_378 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodShrink_250 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_prodShrink_702
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.prodTailShrink
d_prodTailShrink_252 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_380 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodTailShrink_252 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_prodTailShrink_712
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.sumShrink
d_sumShrink_262 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_382 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumShrink_262 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_sumShrink_720
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.sumTailShrink
d_sumTailShrink_264 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_384 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumTailShrink_264 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_sumTailShrink_730
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.arrowTailP
d_arrowTailP_356 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_356
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_136
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.atomKw
d_atomKw_358 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_358
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_148
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.atomP
d_atomP_360 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_360
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_124
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fAtomP
d_fAtomP_362 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_362
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_138
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fProdP
d_fProdP_364 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_364
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_140
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fProdTailP
d_fProdTailP_366 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_366
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_144
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fSumP
d_fSumP_368 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_368
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_142
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fSumTailP
d_fSumTailP_370 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_370
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_146
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuActWith
d_nuActWith_372 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuActWith_372 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuActWith_168
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.nuCloseActP
d_nuCloseActP_374 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuCloseActP_374
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuCloseActP_170
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuCloseP
d_nuCloseP_376 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuCloseP_376
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuCloseP_156
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuEffP
d_nuEffP_378 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuEffP_378
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuEffP_152
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuEffWith
d_nuEffWith_380 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuEffWith_380
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuEffWith_162
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuP
d_nuP_382 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuP_382
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuP_150
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuTryP
d_nuTryP_384 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuTryP_384
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuTryP_154
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.typeP
d_typeP_386 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_386
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_130
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.prodP
d_prodP_388 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_388
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_126
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.prodTailP
d_prodTailP_390 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_390
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_132
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sumP
d_sumP_392 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_392
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_128
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sumTailP
d_sumTailP_394 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_394
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_134
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sound-arrowTail
d_sound'45'arrowTail_398 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_388
d_sound'45'arrowTail_398 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_422
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-atom
d_sound'45'atom_400 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376
d_sound'45'atom_400 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'atom_332
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fAtom
d_sound'45'fAtom_402 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_390
d_sound'45'fAtom_402 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fAtom_432
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fProd
d_sound'45'fProd_404 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_392
d_sound'45'fProd_404 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProd_442
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fProdTail
d_sound'45'fProdTail_406 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_394
d_sound'45'fProdTail_406 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProdTail_454
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-fSum
d_sound'45'fSum_408 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_396
d_sound'45'fSum_408 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSum_464
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fSumTail
d_sound'45'fSumTail_410 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_398
d_sound'45'fSumTail_410 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSumTail_476
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-kw
d_sound'45'kw_412 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376
d_sound'45'kw_412 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_356
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-nuEff
d_sound'45'nuEff_414 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376
d_sound'45'nuEff_414 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'nuEff_346
      (coe d_PolyAlg_118) v0 v1
-- Once.Parser.Generic.PolyInst._.sound-type
d_sound'45'type_416 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_386
d_sound'45'type_416 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'type_410
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-prod
d_sound'45'prod_418 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_378
d_sound'45'prod_418 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prod_366
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-prodTail
d_sound'45'prodTail_420 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_380
d_sound'45'prodTail_420 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_378
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-sum
d_sound'45'sum_422 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_382
d_sound'45'sum_422 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sum_388
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-sumTail
d_sound'45'sumTail_424 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_384
d_sound'45'sumTail_424 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_400
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.complete-arrowTail
d_complete'45'arrowTail_428 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_388 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_428 = erased
-- Once.Parser.Generic.PolyInst._.complete-atom
d_complete'45'atom_430 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_430 = erased
-- Once.Parser.Generic.PolyInst._.complete-fAtom
d_complete'45'fAtom_432 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_390 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_432 = erased
-- Once.Parser.Generic.PolyInst._.complete-fProd
d_complete'45'fProd_434 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_392 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_434 = erased
-- Once.Parser.Generic.PolyInst._.complete-fProdTail
d_complete'45'fProdTail_436 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_436 = erased
-- Once.Parser.Generic.PolyInst._.complete-fSum
d_complete'45'fSum_438 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_438 = erased
-- Once.Parser.Generic.PolyInst._.complete-fSumTail
d_complete'45'fSumTail_440 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_398 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_440 = erased
-- Once.Parser.Generic.PolyInst._.complete-type
d_complete'45'type_442 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_442 = erased
-- Once.Parser.Generic.PolyInst._.complete-prod
d_complete'45'prod_444 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_444 = erased
-- Once.Parser.Generic.PolyInst._.complete-prodTail
d_complete'45'prodTail_446 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_446 = erased
-- Once.Parser.Generic.PolyInst._.complete-sum
d_complete'45'sum_448 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_448 = erased
-- Once.Parser.Generic.PolyInst._.complete-sumTail
d_complete'45'sumTail_450 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_450 = erased
-- Once.Parser.Generic.PolyInst._.fSum-parenAct
d_fSum'45'parenAct_452 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenAct_452 = erased
-- Once.Parser.Generic.PolyInst._.fSum-parenEff
d_fSum'45'parenEff_454 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenEff_454 = erased
