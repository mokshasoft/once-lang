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
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Surface.Type

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
                (coe MAlonzo.Code.Once.Spec.Surface.Type.C_PTVar_42 (coe v0))
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
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
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
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_TVarRel_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tvar'45'complete_110 = erased
-- Once.Parser.Generic.PolyInst.PolyAlg
d_PolyAlg_118 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46
d_PolyAlg_118
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.C_constructor_248
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C_PUnit_20)
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C_PVoid_22)
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C_PInt_24)
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C_PFloat_26)
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C__P'42'__28)
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C__P'43'__30)
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C_PEff_36)
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C_PAct_34)
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Once.Spec.Surface.Type.C__P'8658''91'_'93'__32
           (coe v1) (coe v0))
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C_Pμ_38)
      (\ v0 ->
         coe
           MAlonzo.Code.Once.Spec.Surface.Type.C_Pν_40 (coe v0)
           (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
      (\ v0 ->
         coe
           MAlonzo.Code.Once.Spec.Surface.Type.C_Pν_40 (coe v0)
           (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C_PK_12)
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C_PId_14)
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C__P'8853'__16)
      (coe MAlonzo.Code.Once.Spec.Surface.Type.C__P'8855'__18)
      (\ v0 v1 v2 v3 -> coe du_tvar'45'shrink_58 v2 v3) d_tvarP_46
-- Once.Parser.Generic.PolyInst.Gen′.ParsesTypeG
d_ParsesTypeG_150 a0 a1 a2 = ()
-- Once.Parser.Generic.PolyInst.Gen′.typeShrink
d_typeShrink_152 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_typeShrink_152 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Relation.du_typeShrink_716
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst.Make′′.arrowTailP
d_arrowTailP_160 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_160
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_110
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.atomKw
d_atomKw_162 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_162
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_122
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.atomP
d_atomP_164 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_164
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_98
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.fAtomP
d_fAtomP_166 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_166
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_112
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.fProdP
d_fProdP_168 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_168
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_114
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.fProdTailP
d_fProdTailP_170 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_170
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_118
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.fSumP
d_fSumP_172 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_172
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_116
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.fSumTailP
d_fSumTailP_174 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_174
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_120
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.nuActWith
d_nuActWith_176 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuActWith_176 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuActWith_132
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′′.nuCloseActP
d_nuCloseActP_178 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuCloseActP_178
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuCloseActP_134
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.nuP
d_nuP_180 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuP_180
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuP_124
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.nuTryP
d_nuTryP_182 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuTryP_182
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuTryP_126
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.typeP
d_typeP_184 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_184
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_104
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.prodP
d_prodP_186 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_186
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_100
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.prodTailP
d_prodTailP_188 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_188
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_106
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.sumP
d_sumP_190 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_190
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_102
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.sumTailP
d_sumTailP_192 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_192
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_108
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′.sound-arrowTail
d_sound'45'arrowTail_196 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372
d_sound'45'arrowTail_196 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_404
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′.sound-atom
d_sound'45'atom_198 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_sound'45'atom_198 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'atom_314
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′.sound-fAtom
d_sound'45'fAtom_200 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374
d_sound'45'fAtom_200 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fAtom_414
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′.sound-fProd
d_sound'45'fProd_202 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376
d_sound'45'fProd_202 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProd_424
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′.sound-fProdTail
d_sound'45'fProdTail_204 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378
d_sound'45'fProdTail_204 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProdTail_436
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′.sound-fSum
d_sound'45'fSum_206 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380
d_sound'45'fSum_206 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSum_446
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′.sound-fSumTail
d_sound'45'fSumTail_208 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382
d_sound'45'fSumTail_208 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSumTail_458
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′.sound-kw
d_sound'45'kw_210 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_sound'45'kw_210 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_338
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′.sound-nuAct
d_sound'45'nuAct_212 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_sound'45'nuAct_212 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'nuAct_328
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′.sound-type
d_sound'45'type_214 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370
d_sound'45'type_214 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'type_392
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst.Make′.sound-prod
d_sound'45'prod_216 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362
d_sound'45'prod_216 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prod_348
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′.sound-prodTail
d_sound'45'prodTail_218 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364
d_sound'45'prodTail_218 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_360
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′.sound-sum
d_sound'45'sum_220 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366
d_sound'45'sum_220 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sum_370
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′.sound-sumTail
d_sound'45'sumTail_222 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368
d_sound'45'sumTail_222 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_382
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make.complete-arrowTail
d_complete'45'arrowTail_226 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_226 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-atom
d_complete'45'atom_228 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_228 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fAtom
d_complete'45'fAtom_230 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_230 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fProd
d_complete'45'fProd_232 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_232 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fProdTail
d_complete'45'fProdTail_234 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_234 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fSum
d_complete'45'fSum_236 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_236 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fSumTail
d_complete'45'fSumTail_238 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_238 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-type
d_complete'45'type_240 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_240 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-prod
d_complete'45'prod_242 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_242 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-prodTail
d_complete'45'prodTail_244 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_244 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-sum
d_complete'45'sum_246 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_246 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-sumTail
d_complete'45'sumTail_248 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_248 = erased
-- Once.Parser.Generic.PolyInst.Make.fSum-parenAct
d_fSum'45'parenAct_250 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenAct_250 = erased
