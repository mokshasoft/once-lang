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
      MAlonzo.Code.Once.Parser.Generic.Relation.C_constructor_252
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
           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
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
d_ParsesArrowTailG_152 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesAtomG
d_ParsesAtomG_154 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncAtomG
d_ParsesFuncAtomG_156 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncProdG
d_ParsesFuncProdG_158 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncProdTailG
d_ParsesFuncProdTailG_160 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncSumG
d_ParsesFuncSumG_162 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesFuncSumTailG
d_ParsesFuncSumTailG_164 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesTypeG
d_ParsesTypeG_166 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.typeShrink
d_typeShrink_168 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_376 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_typeShrink_168 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_typeShrink_730
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst._.ParsesProdG
d_ParsesProdG_170 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesProdTailG
d_ParsesProdTailG_172 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.ParsesSumG
d_ParsesSumG_174 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst._.ParsesSumTailG
d_ParsesSumTailG_176 a0 a1 a2 a3 = ()
-- Once.Parser.Generic.PolyInst._.arrowTailShrink
d_arrowTailShrink_178 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_378 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_arrowTailShrink_178 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_arrowTailShrink_722
      (coe d_PolyAlg_118) v1 v3 v4
-- Once.Parser.Generic.PolyInst._.atomShrink
d_atomShrink_180 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_366 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_atomShrink_180
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.d_atomShrink_676
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.funcAtomShrink
d_funcAtomShrink_182 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_380 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcAtomShrink_182
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.d_funcAtomShrink_738
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.funcProdShrink
d_funcProdShrink_184 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_382 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdShrink_184 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcProdShrink_746
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.funcProdTailShrink
d_funcProdTailShrink_186 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_384 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcProdTailShrink_186 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcProdTailShrink_756
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.funcSumShrink
d_funcSumShrink_188 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_386 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumShrink_188 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcSumShrink_764
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.funcSumTailShrink
d_funcSumTailShrink_190 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_388 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_funcSumTailShrink_190 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_funcSumTailShrink_774
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.prodShrink
d_prodShrink_246 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_368 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodShrink_246 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_prodShrink_684
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.prodTailShrink
d_prodTailShrink_248 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_370 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prodTailShrink_248 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_prodTailShrink_694
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.sumShrink
d_sumShrink_258 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_372 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumShrink_258 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_sumShrink_702
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst._.sumTailShrink
d_sumTailShrink_260 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_374 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sumTailShrink_260 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_sumTailShrink_712
      (coe d_PolyAlg_118) v1 v4
-- Once.Parser.Generic.PolyInst._.arrowTailP
d_arrowTailP_350 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_350
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_134
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.atomKw
d_atomKw_352 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_352
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_146
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.atomP
d_atomP_354 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_354
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_122
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fAtomP
d_fAtomP_356 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_356
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_136
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fProdP
d_fProdP_358 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_358
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_138
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fProdTailP
d_fProdTailP_360 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_360
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_142
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fSumP
d_fSumP_362 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_362
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_140
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.fSumTailP
d_fSumTailP_364 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_364
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_144
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuActWith
d_nuActWith_366 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuActWith_366 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuActWith_166
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.nuCloseActP
d_nuCloseActP_368 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuCloseActP_368
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuCloseActP_168
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuCloseP
d_nuCloseP_370 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuCloseP_370
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuCloseP_154
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuEffP
d_nuEffP_372 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuEffP_372
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuEffP_150
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuEffWith
d_nuEffWith_374 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuEffWith_374
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuEffWith_160
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuP
d_nuP_376 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuP_376
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuP_148
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.nuTryP
d_nuTryP_378 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuTryP_378
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuTryP_152
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.typeP
d_typeP_380 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_380
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_128
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.prodP
d_prodP_382 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_382
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_124
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.prodTailP
d_prodTailP_384 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_384
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_130
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sumP
d_sumP_386 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_386
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_126
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sumTailP
d_sumTailP_388 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_388
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_132
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst._.sound-arrowTail
d_sound'45'arrowTail_392 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_378
d_sound'45'arrowTail_392 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_416
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-atom
d_sound'45'atom_394 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_366
d_sound'45'atom_394 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'atom_326
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fAtom
d_sound'45'fAtom_396 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_380
d_sound'45'fAtom_396 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fAtom_426
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fProd
d_sound'45'fProd_398 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_382
d_sound'45'fProd_398 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProd_436
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fProdTail
d_sound'45'fProdTail_400 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_384
d_sound'45'fProdTail_400 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProdTail_448
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-fSum
d_sound'45'fSum_402 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_386
d_sound'45'fSum_402 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSum_458
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-fSumTail
d_sound'45'fSumTail_404 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_388
d_sound'45'fSumTail_404 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSumTail_470
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-kw
d_sound'45'kw_406 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_366
d_sound'45'kw_406 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_350
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-nuEff
d_sound'45'nuEff_408 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_366
d_sound'45'nuEff_408 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'nuEff_340
      (coe d_PolyAlg_118) v0 v1
-- Once.Parser.Generic.PolyInst._.sound-type
d_sound'45'type_410 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_376
d_sound'45'type_410 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'type_404
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-prod
d_sound'45'prod_412 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_368
d_sound'45'prod_412 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prod_360
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-prodTail
d_sound'45'prodTail_414 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_370
d_sound'45'prodTail_414 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_372
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.sound-sum
d_sound'45'sum_416 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_372
d_sound'45'sum_416 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sum_382
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst._.sound-sumTail
d_sound'45'sumTail_418 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_374
d_sound'45'sumTail_418 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_394
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst._.complete-arrowTail
d_complete'45'arrowTail_422 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_422 = erased
-- Once.Parser.Generic.PolyInst._.complete-atom
d_complete'45'atom_424 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_424 = erased
-- Once.Parser.Generic.PolyInst._.complete-fAtom
d_complete'45'fAtom_426 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_426 = erased
-- Once.Parser.Generic.PolyInst._.complete-fProd
d_complete'45'fProd_428 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_428 = erased
-- Once.Parser.Generic.PolyInst._.complete-fProdTail
d_complete'45'fProdTail_430 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_430 = erased
-- Once.Parser.Generic.PolyInst._.complete-fSum
d_complete'45'fSum_432 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_386 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_432 = erased
-- Once.Parser.Generic.PolyInst._.complete-fSumTail
d_complete'45'fSumTail_434 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_388 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_434 = erased
-- Once.Parser.Generic.PolyInst._.complete-type
d_complete'45'type_436 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_436 = erased
-- Once.Parser.Generic.PolyInst._.complete-prod
d_complete'45'prod_438 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_438 = erased
-- Once.Parser.Generic.PolyInst._.complete-prodTail
d_complete'45'prodTail_440 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_370 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_440 = erased
-- Once.Parser.Generic.PolyInst._.complete-sum
d_complete'45'sum_442 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_372 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_442 = erased
-- Once.Parser.Generic.PolyInst._.complete-sumTail
d_complete'45'sumTail_444 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_444 = erased
-- Once.Parser.Generic.PolyInst._.fSum-parenAct
d_fSum'45'parenAct_446 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenAct_446 = erased
-- Once.Parser.Generic.PolyInst._.fSum-parenEff
d_fSum'45'parenEff_448 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenEff_448 = erased
