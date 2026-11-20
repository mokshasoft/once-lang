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
-- Once.Parser.Generic.PolyInst.Make′′.arrK
d_arrK_160 ::
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrK_160 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_arrK_444 v0 v2 v3 v4
-- Once.Parser.Generic.PolyInst.Make′′.arrowTailA
d_arrowTailA_162 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailA_162 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_arrowTailA_564
      (coe d_PolyAlg_118) v0 v1
-- Once.Parser.Generic.PolyInst.Make′′.arrowTailP
d_arrowTailP_164 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_164
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_arrowTailP_1116
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.atGo
d_atGo_166 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atGo_166 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atGo_572
      (coe d_PolyAlg_118) v0 v1 v2 v3 v4
-- Once.Parser.Generic.PolyInst.Make′′.atomA
d_atomA_168 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomA_168 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomA_470
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′′.atomH
d_atomH_170 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_HeadV_246 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomH_170 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomH_486
      (coe d_PolyAlg_118) v0 v1
-- Once.Parser.Generic.PolyInst.Make′′.atomKw
d_atomKw_172 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_172 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomKw_482
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′′.atomP
d_atomP_174 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_174
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_atomP_1096
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.atomX
d_atomX_176 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomX_176 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_atomX_478
      (coe d_PolyAlg_118) v0 v2
-- Once.Parser.Generic.PolyInst.Make′′.fAtomA
d_fAtomA_178 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomA_178 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fAtomA_576
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′′.fAtomH
d_fAtomH_180 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_HeadV_246 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomH_180 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fAtomH_580
      (coe d_PolyAlg_118) v0 v1
-- Once.Parser.Generic.PolyInst.Make′′.fAtomP
d_fAtomP_182 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_182
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fAtomP_1130
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.fProdA
d_fProdA_184 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdA_184 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdA_590
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′′.fProdK
d_fProdK_186 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdK_186 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdK_594
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′′.fProdP
d_fProdP_188 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_188
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdP_1132
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.fProdTailA
d_fProdTailA_190 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailA_190 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fProdTailA_598
      (coe d_PolyAlg_118) v0 v1
-- Once.Parser.Generic.PolyInst.Make′′.fProdTailP
d_fProdTailP_192 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_192
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fProdTailP_1142
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.fSumA
d_fSumA_194 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumA_194 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumA_612
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′′.fSumK
d_fSumK_196 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumK_196 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumK_616
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′′.fSumP
d_fSumP_198 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_198
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumP_1134
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.fSumTailA
d_fSumTailA_200 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailA_200 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fSumTailA_620
      (coe d_PolyAlg_118) v0 v1
-- Once.Parser.Generic.PolyInst.Make′′.fSumTailP
d_fSumTailP_202 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_202
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_fSumTailP_1144
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.fkwK
d_fkwK_204 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_FKwV_186 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fkwK_204 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fkwK_586
      (coe d_PolyAlg_118) v1 v2
-- Once.Parser.Generic.PolyInst.Make′′.fptGo
d_fptGo_206 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fptGo_206 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fptGo_604
      (coe d_PolyAlg_118) v0 v1 v2 v3
-- Once.Parser.Generic.PolyInst.Make′′.fptK
d_fptK_208 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fptK_208 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fptK_608
      (coe d_PolyAlg_118) v0 v1 v2 v3
-- Once.Parser.Generic.PolyInst.Make′′.fstGo
d_fstGo_210 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fstGo_210 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fstGo_626
      (coe d_PolyAlg_118) v0 v1 v2 v3
-- Once.Parser.Generic.PolyInst.Make′′.fstK
d_fstK_212 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fstK_212 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_fstK_630
      (coe d_PolyAlg_118) v0 v1 v2 v3
-- Once.Parser.Generic.PolyInst.Make′′.kwK
d_kwK_214 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_KwV_124 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_kwK_214 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_kwK_492
      (coe d_PolyAlg_118) v1 v2
-- Once.Parser.Generic.PolyInst.Make′′.nuAct
d_nuAct_216 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuAct_216 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuAct_508
      (coe d_PolyAlg_118) v2
-- Once.Parser.Generic.PolyInst.Make′′.nuC
d_nuC_218 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_CloseV_274 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuC_218
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuC_366
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.nuClose
d_nuClose_220 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuClose_220
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_nuClose_386
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.nuTry
d_nuTry_222 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuTry_222 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_nuTry_502
      (coe d_PolyAlg_118) v0 v2
-- Once.Parser.Generic.PolyInst.Make′′.parenC
d_parenC_224 ::
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_CloseV_274 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parenC_224 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_parenC_406 v1 v2 v3 v4
      v5
-- Once.Parser.Generic.PolyInst.Make′′.parenK
d_parenK_226 ::
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parenK_226 v0 v1 v2
  = coe MAlonzo.Code.Once.Parser.Generic.Parser.du_parenK_428 v1 v2
-- Once.Parser.Generic.PolyInst.Make′′.typeP
d_typeP_228 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_228
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_1102
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.prodA
d_prodA_230 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodA_230 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_prodA_512
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′′.prodK
d_prodK_232 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodK_232 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_prodK_516
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′′.prodP
d_prodP_234 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_234
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodP_1098
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.prodTailA
d_prodTailA_236 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailA_236 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_prodTailA_520
      (coe d_PolyAlg_118) v0 v1
-- Once.Parser.Generic.PolyInst.Make′′.prodTailP
d_prodTailP_238 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_238
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_1112
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.ptGo
d_ptGo_240 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ptGo_240 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_ptGo_526
      (coe d_PolyAlg_118) v0 v1 v2 v3
-- Once.Parser.Generic.PolyInst.Make′′.ptK
d_ptK_242 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ptK_242 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_ptK_530
      (coe d_PolyAlg_118) v0 v1 v2 v3
-- Once.Parser.Generic.PolyInst.Make′′.stGo
d_stGo_244 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stGo_244 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_stGo_548
      (coe d_PolyAlg_118) v0 v1 v2 v3
-- Once.Parser.Generic.PolyInst.Make′′.stK
d_stK_246 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stK_246 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_stK_552
      (coe d_PolyAlg_118) v0 v1 v2 v3
-- Once.Parser.Generic.PolyInst.Make′′.sumA
d_sumA_248 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumA_248 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_sumA_534
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′′.sumK
d_sumK_250 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumK_250 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_sumK_538
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′′.sumP
d_sumP_252 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_252
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumP_1100
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.sumTailA
d_sumTailA_254 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailA_254 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_sumTailA_542
      (coe d_PolyAlg_118) v0 v1
-- Once.Parser.Generic.PolyInst.Make′′.sumTailP
d_sumTailP_256 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_256
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_1114
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′′.twoK
d_twoK_258 ::
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_twoK_258 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_twoK_498
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst.Make′′.typeA
d_typeA_260 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeA_260 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_typeA_556
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′′.typeK
d_typeK_262 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeK_262 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Parser.du_typeK_560
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′.BG
d_BG_266 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 -> ()
d_BG_266 = erased
-- Once.Parser.Generic.PolyInst.Make′.arrK-sound
d_arrK'45'sound_268 ::
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()) ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_arrK'45'sound_268 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_arrK'45'sound_630 v4 v8
-- Once.Parser.Generic.PolyInst.Make′.atGo-sound
d_atGo'45'sound_270 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372
d_atGo'45'sound_270 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_atGo'45'sound_962
      (coe d_PolyAlg_118) v1 v2
-- Once.Parser.Generic.PolyInst.Make′.atomH-sound
d_atomH'45'sound_272 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_HeadV_246 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_atomH'45'sound_272 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_atomH'45'sound_688
      (coe d_PolyAlg_118) v0 v1 v4
-- Once.Parser.Generic.PolyInst.Make′.atomX-sound
d_atomX'45'sound_274 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_atomX'45'sound_274 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_atomX'45'sound_588 v2 v3
      v4 v5 v6
-- Once.Parser.Generic.PolyInst.Make′.fAtomH-sound
d_fAtomH'45'sound_276 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_HeadV_246 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374
d_fAtomH'45'sound_276 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_fAtomH'45'sound_984
      (coe d_PolyAlg_118) v0 v1 v4
-- Once.Parser.Generic.PolyInst.Make′.fProdK-sound
d_fProdK'45'sound_278 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376
d_fProdK'45'sound_278 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_fProdK'45'sound_1024
      (coe d_PolyAlg_118) v1 v3 v4 v5
-- Once.Parser.Generic.PolyInst.Make′.fSumK-sound
d_fSumK'45'sound_280 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380
d_fSumK'45'sound_280 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_fSumK'45'sound_1098
      (coe d_PolyAlg_118) v1 v3 v4 v5
-- Once.Parser.Generic.PolyInst.Make′.fkwK-sound
d_fkwK'45'sound_282 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_FKwV_186 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374
d_fkwK'45'sound_282 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_fkwK'45'sound_998
      (coe d_PolyAlg_118) v1 v2
-- Once.Parser.Generic.PolyInst.Make′.fptGo-sound
d_fptGo'45'sound_284 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378
d_fptGo'45'sound_284 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_fptGo'45'sound_1052
      (coe d_PolyAlg_118) v0 v1 v2 v5 v6
-- Once.Parser.Generic.PolyInst.Make′.fptK-sound
d_fptK'45'sound_286 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378
d_fptK'45'sound_286 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_fptK'45'sound_1072
      (coe d_PolyAlg_118) v0 v3 v5 v6 v8
-- Once.Parser.Generic.PolyInst.Make′.fstGo-sound
d_fstGo'45'sound_288 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382
d_fstGo'45'sound_288 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_fstGo'45'sound_1126
      (coe d_PolyAlg_118) v0 v1 v2 v5 v6
-- Once.Parser.Generic.PolyInst.Make′.fstK-sound
d_fstK'45'sound_290 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382
d_fstK'45'sound_290 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_fstK'45'sound_1146
      (coe d_PolyAlg_118) v0 v3 v5 v6 v8
-- Once.Parser.Generic.PolyInst.Make′.kwK-sound
d_kwK'45'sound_292 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_KwV_124 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_kwK'45'sound_292 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_kwK'45'sound_702
      (coe d_PolyAlg_118) v1 v2
-- Once.Parser.Generic.PolyInst.Make′.nuAct-sound
d_nuAct'45'sound_294 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_nuAct'45'sound_294 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_nuAct'45'sound_758
      (coe d_PolyAlg_118) v2
-- Once.Parser.Generic.PolyInst.Make′.nuC-sound
d_nuC'45'sound_296 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Parser.Generic.Parser.T_CloseV_274 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_nuC'45'sound_296 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_nuC'45'sound_522 v1 v4 v7
-- Once.Parser.Generic.PolyInst.Make′.nuClose-sound
d_nuClose'45'sound_298 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_nuClose'45'sound_298 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_nuClose'45'sound_556 v1
      v4
-- Once.Parser.Generic.PolyInst.Make′.nuTry-sound
d_nuTry'45'sound_300 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_nuTry'45'sound_300 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_nuTry'45'sound_746
      (coe d_PolyAlg_118) v0 v2 v5
-- Once.Parser.Generic.PolyInst.Make′.parenC-sound
d_parenC'45'sound_302 ::
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
d_parenC'45'sound_302 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_parenC'45'sound_450 v6 v9
-- Once.Parser.Generic.PolyInst.Make′.parenK-sound
d_parenK'45'sound_304 ::
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
d_parenK'45'sound_304 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_parenK'45'sound_488 v3 v6
-- Once.Parser.Generic.PolyInst.Make′.prodK-sound
d_prodK'45'sound_306 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362
d_prodK'45'sound_306 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_prodK'45'sound_784
      (coe d_PolyAlg_118) v1 v3 v4 v5
-- Once.Parser.Generic.PolyInst.Make′.ptGo-sound
d_ptGo'45'sound_308 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364
d_ptGo'45'sound_308 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_ptGo'45'sound_812
      (coe d_PolyAlg_118) v0 v1 v2 v5 v6
-- Once.Parser.Generic.PolyInst.Make′.ptK-sound
d_ptK'45'sound_310 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364
d_ptK'45'sound_310 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_ptK'45'sound_832
      (coe d_PolyAlg_118) v0 v3 v5 v6 v8
-- Once.Parser.Generic.PolyInst.Make′.sound-arrowTail
d_sound'45'arrowTail_312 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372
d_sound'45'arrowTail_312 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_944
      (coe d_PolyAlg_118) v1
-- Once.Parser.Generic.PolyInst.Make′.sound-atom
d_sound'45'atom_314 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_sound'45'atom_314 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'atom_676
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst.Make′.sound-atomP
d_sound'45'atomP_316 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_sound'45'atomP_316
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.d_sound'45'atomP_1776
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′.sound-fAtom
d_sound'45'fAtom_318 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374
d_sound'45'fAtom_318 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fAtom_972
      (coe d_PolyAlg_118) v0 v3
-- Once.Parser.Generic.PolyInst.Make′.sound-fProd
d_sound'45'fProd_320 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376
d_sound'45'fProd_320 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProd_1008
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst.Make′.sound-fProdTail
d_sound'45'fProdTail_322 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378
d_sound'45'fProdTail_322 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fProdTail_1036
      (coe d_PolyAlg_118) v0 v1 v3 v4
-- Once.Parser.Generic.PolyInst.Make′.sound-fSum
d_sound'45'fSum_324 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380
d_sound'45'fSum_324 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSum_1082
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst.Make′.sound-fSumP
d_sound'45'fSumP_326 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380
d_sound'45'fSumP_326
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.d_sound'45'fSumP_1796
      (coe d_PolyAlg_118)
-- Once.Parser.Generic.PolyInst.Make′.sound-fSumTail
d_sound'45'fSumTail_328 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382
d_sound'45'fSumTail_328 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'fSumTail_1110
      (coe d_PolyAlg_118) v0 v1 v3 v4
-- Once.Parser.Generic.PolyInst.Make′.sound-type
d_sound'45'type_330 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370
d_sound'45'type_330 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'type_916
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′.sound-prod
d_sound'45'prod_332 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362
d_sound'45'prod_332 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prod_768
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst.Make′.sound-prodTail
d_sound'45'prodTail_334 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364
d_sound'45'prodTail_334 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_796
      (coe d_PolyAlg_118) v0 v1 v3 v4
-- Once.Parser.Generic.PolyInst.Make′.sound-sum
d_sound'45'sum_336 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366
d_sound'45'sum_336 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sum_842
      (coe d_PolyAlg_118) v0 v2 v3
-- Once.Parser.Generic.PolyInst.Make′.sound-sumTail
d_sound'45'sumTail_338 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368
d_sound'45'sumTail_338 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_870
      (coe d_PolyAlg_118) v0 v1 v3 v4
-- Once.Parser.Generic.PolyInst.Make′.sound-typeP
d_sound'45'typeP_340 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370
d_sound'45'typeP_340 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'typeP_1786
      (coe d_PolyAlg_118) v0
-- Once.Parser.Generic.PolyInst.Make′.stGo-sound
d_stGo'45'sound_342 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368
d_stGo'45'sound_342 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_stGo'45'sound_886
      (coe d_PolyAlg_118) v0 v1 v2 v5 v6
-- Once.Parser.Generic.PolyInst.Make′.stK-sound
d_stK'45'sound_344 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368
d_stK'45'sound_344 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_stK'45'sound_906
      (coe d_PolyAlg_118) v0 v3 v5 v6 v8
-- Once.Parser.Generic.PolyInst.Make′.sumK-sound
d_sumK'45'sound_346 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366
d_sumK'45'sound_346 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_sumK'45'sound_858
      (coe d_PolyAlg_118) v1 v3 v4 v5
-- Once.Parser.Generic.PolyInst.Make′.twoK-sound
d_twoK'45'sound_348 ::
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360
d_twoK'45'sound_348 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_twoK'45'sound_730
      (coe d_PolyAlg_118) v3 v7 v8
-- Once.Parser.Generic.PolyInst.Make′.typeK-sound
d_typeK'45'sound_350 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370
d_typeK'45'sound_350 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.Generic.Sound.du_typeK'45'sound_932
      (coe d_PolyAlg_118) v1 v5
-- Once.Parser.Generic.PolyInst.Make.arrK-ok
d_arrK'45'ok_354 ::
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arrK'45'ok_354 = erased
-- Once.Parser.Generic.PolyInst.Make.atGo-A
d_atGo'45'A_356 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atGo'45'A_356 = erased
-- Once.Parser.Generic.PolyInst.Make.atGo-G
d_atGo'45'G_358 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atGo'45'G_358 = erased
-- Once.Parser.Generic.PolyInst.Make.atGo-done
d_atGo'45'done_360 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
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
d_atGo'45'done_360 = erased
-- Once.Parser.Generic.PolyInst.Make.atomX-hit
d_atomX'45'hit_362 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_TVarRel_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atomX'45'hit_362 = erased
-- Once.Parser.Generic.PolyInst.Make.atomX-miss
d_atomX'45'miss_364 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atomX'45'miss_364 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-arrowTail
d_complete'45'arrowTail_366 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTail_366 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-arrowTailA
d_complete'45'arrowTailA_368 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesArrowTailG_372 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'arrowTailA_368 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-atom
d_complete'45'atom_370 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atom_370 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-atomA
d_complete'45'atomA_372 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesAtomG_360 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'atomA_372 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fAtom
d_complete'45'fAtom_374 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtom_374 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fAtomA
d_complete'45'fAtomA_376 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncAtomG_374 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fAtomA_376 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fProd
d_complete'45'fProd_378 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProd_378 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fProdA
d_complete'45'fProdA_380 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdG_376 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdA_380 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fProdTail
d_complete'45'fProdTail_382 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTail_382 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fProdTailA
d_complete'45'fProdTailA_384 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncProdTailG_378 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fProdTailA_384 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fSum
d_complete'45'fSum_386 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSum_386 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fSumA
d_complete'45'fSumA_388 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumG_380 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumA_388 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fSumTail
d_complete'45'fSumTail_390 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTail_390 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-fSumTailA
d_complete'45'fSumTailA_392 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesFuncSumTailG_382 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'fSumTailA_392 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-type
d_complete'45'type_394 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'type_394 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-prod
d_complete'45'prod_396 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prod_396 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-prodA
d_complete'45'prodA_398 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdG_362 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodA_398 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-prodTail
d_complete'45'prodTail_400 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTail_400 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-prodTailA
d_complete'45'prodTailA_402 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesProdTailG_364 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'prodTailA_402 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-sum
d_complete'45'sum_404 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sum_404 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-sumA
d_complete'45'sumA_406 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumG_366 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumA_406 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-sumTail
d_complete'45'sumTail_408 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTail_408 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-sumTailA
d_complete'45'sumTailA_410 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesSumTailG_368 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'sumTailA_410 = erased
-- Once.Parser.Generic.PolyInst.Make.complete-typeA
d_complete'45'typeA_412 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_370 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'typeA_412 = erased
-- Once.Parser.Generic.PolyInst.Make.fProdK-ok
d_fProdK'45'ok_414 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fProdK'45'ok_414 = erased
-- Once.Parser.Generic.PolyInst.Make.fSum-parenAct
d_fSum'45'parenAct_416 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSum'45'parenAct_416 = erased
-- Once.Parser.Generic.PolyInst.Make.fSumK-ok
d_fSumK'45'ok_418 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fSumK'45'ok_418 = erased
-- Once.Parser.Generic.PolyInst.Make.fptGo-done
d_fptGo'45'done_420 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fptGo'45'done_420 = erased
-- Once.Parser.Generic.PolyInst.Make.fptGo-star
d_fptGo'45'star_422 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fptGo'45'star_422 = erased
-- Once.Parser.Generic.PolyInst.Make.fptK-ok
d_fptK'45'ok_424 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fptK'45'ok_424 = erased
-- Once.Parser.Generic.PolyInst.Make.fstGo-done
d_fstGo'45'done_426 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fstGo'45'done_426 = erased
-- Once.Parser.Generic.PolyInst.Make.fstGo-plus
d_fstGo'45'plus_428 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fstGo'45'plus_428 = erased
-- Once.Parser.Generic.PolyInst.Make.fstK-ok
d_fstK'45'ok_430 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fstK'45'ok_430 = erased
-- Once.Parser.Generic.PolyInst.Make.nuClose-ok
d_nuClose'45'ok_432 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nuClose'45'ok_432 = erased
-- Once.Parser.Generic.PolyInst.Make.nuTry-just
d_nuTry'45'just_434 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyFunctor_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nuTry'45'just_434 = erased
-- Once.Parser.Generic.PolyInst.Make.nuTry-nothing
d_nuTry'45'nothing_436 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nuTry'45'nothing_436 = erased
-- Once.Parser.Generic.PolyInst.Make.parenK-ok
d_parenK'45'ok_438 ::
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parenK'45'ok_438 = erased
-- Once.Parser.Generic.PolyInst.Make.prodK-ok
d_prodK'45'ok_440 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prodK'45'ok_440 = erased
-- Once.Parser.Generic.PolyInst.Make.ptGo-done
d_ptGo'45'done_442 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ptGo'45'done_442 = erased
-- Once.Parser.Generic.PolyInst.Make.ptGo-star
d_ptGo'45'star_444 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ptGo'45'star_444 = erased
-- Once.Parser.Generic.PolyInst.Make.ptK-ok
d_ptK'45'ok_446 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ptK'45'ok_446 = erased
-- Once.Parser.Generic.PolyInst.Make.stGo-done
d_stGo'45'done_448 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stGo'45'done_448 = erased
-- Once.Parser.Generic.PolyInst.Make.stGo-plus
d_stGo'45'plus_450 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stGo'45'plus_450 = erased
-- Once.Parser.Generic.PolyInst.Make.stK-ok
d_stK'45'ok_452 ::
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stK'45'ok_452 = erased
-- Once.Parser.Generic.PolyInst.Make.sumK-ok
d_sumK'45'ok_454 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sumK'45'ok_454 = erased
-- Once.Parser.Generic.PolyInst.Make.twoK-ok
d_twoK'45'ok_456 ::
  (MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
   MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_twoK'45'ok_456 = erased
-- Once.Parser.Generic.PolyInst.Make.typeK-ok
d_typeK'45'ok_458 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_typeK'45'ok_458 = erased
