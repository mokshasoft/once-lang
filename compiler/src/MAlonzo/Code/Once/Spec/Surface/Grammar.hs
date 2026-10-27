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

module MAlonzo.Code.Once.Spec.Surface.Grammar where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Surface.Lexing
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.Surface.Grammar.Starts
d_Starts_8 a0 a1 = ()
data T_Starts_8 = C_starts_14
-- Once.Spec.Surface.Grammar.StartsWord
d_StartsWord_16 a0 = ()
data T_StartsWord_16 = C_starts'45'word_22
-- Once.Spec.Surface.Grammar.GradeToken
d_GradeToken_24 a0 a1 = ()
data T_GradeToken_24 = C_g0_26 | C_g1_28 | C_gw_30
-- Once.Spec.Surface.Grammar.TypeAlg
d_TypeAlg_36 a0 a1 = ()
data T_TypeAlg_36
  = C_constructor_106 AgdaAny AgdaAny AgdaAny AgdaAny
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                      (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
                       AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny)
                      (MAlonzo.Code.Once.Spec.Grade.T_Finite_34 -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny) AgdaAny (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
-- Once.Spec.Surface.Grammar.TypeAlg.aUnit
d_aUnit_74 :: T_TypeAlg_36 -> AgdaAny
d_aUnit_74 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.aVoid
d_aVoid_76 :: T_TypeAlg_36 -> AgdaAny
d_aVoid_76 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.aInt
d_aInt_78 :: T_TypeAlg_36 -> AgdaAny
d_aInt_78 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.aFloat
d_aFloat_80 :: T_TypeAlg_36 -> AgdaAny
d_aFloat_80 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.aProd
d_aProd_82 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_aProd_82 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.aSum
d_aSum_84 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_aSum_84 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.aEff
d_aEff_86 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_aEff_86 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.aAct
d_aAct_88 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_aAct_88 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.aArrow
d_aArrow_90 ::
  T_TypeAlg_36 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_aArrow_90 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.aMu
d_aMu_92 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny
d_aMu_92 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.aNu
d_aNu_94 ::
  T_TypeAlg_36 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 -> AgdaAny -> AgdaAny
d_aNu_94 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.fK
d_fK_96 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny
d_fK_96 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.fId
d_fId_98 :: T_TypeAlg_36 -> AgdaAny
d_fId_98 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.fSum
d_fSum_100 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_fSum_100 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.fProd
d_fProd_102 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_fProd_102 v0
  = case coe v0 of
      C_constructor_106 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeAlg.Extra
d_Extra_104 ::
  T_TypeAlg_36 ->
  [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8] ->
  AgdaAny -> [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8] -> ()
d_Extra_104 = erased
-- Once.Spec.Surface.Grammar.Types._.Extra
d_Extra_118 ::
  T_TypeAlg_36 ->
  [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8] ->
  AgdaAny -> [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8] -> ()
d_Extra_118 = erased
-- Once.Spec.Surface.Grammar.Types._.aAct
d_aAct_120 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_aAct_120 v0 = coe d_aAct_88 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.aArrow
d_aArrow_122 ::
  T_TypeAlg_36 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_aArrow_122 v0 = coe d_aArrow_90 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.aEff
d_aEff_124 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_aEff_124 v0 = coe d_aEff_86 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.aFloat
d_aFloat_126 :: T_TypeAlg_36 -> AgdaAny
d_aFloat_126 v0 = coe d_aFloat_80 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.aInt
d_aInt_128 :: T_TypeAlg_36 -> AgdaAny
d_aInt_128 v0 = coe d_aInt_78 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.aMu
d_aMu_130 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny
d_aMu_130 v0 = coe d_aMu_92 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.aNu
d_aNu_132 ::
  T_TypeAlg_36 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 -> AgdaAny -> AgdaAny
d_aNu_132 v0 = coe d_aNu_94 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.aProd
d_aProd_134 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_aProd_134 v0 = coe d_aProd_82 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.aSum
d_aSum_136 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_aSum_136 v0 = coe d_aSum_84 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.aUnit
d_aUnit_138 :: T_TypeAlg_36 -> AgdaAny
d_aUnit_138 v0 = coe d_aUnit_74 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.aVoid
d_aVoid_140 :: T_TypeAlg_36 -> AgdaAny
d_aVoid_140 v0 = coe d_aVoid_76 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.fId
d_fId_142 :: T_TypeAlg_36 -> AgdaAny
d_fId_142 v0 = coe d_fId_98 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.fK
d_fK_144 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny
d_fK_144 v0 = coe d_fK_96 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.fProd
d_fProd_146 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_fProd_146 v0 = coe d_fProd_102 (coe v0)
-- Once.Spec.Surface.Grammar.Types._.fSum
d_fSum_148 :: T_TypeAlg_36 -> AgdaAny -> AgdaAny -> AgdaAny
d_fSum_148 v0 = coe d_fSum_100 (coe v0)
-- Once.Spec.Surface.Grammar.Types.ParsesAtom
d_ParsesAtom_150 a0 a1 a2 a3 a4 a5 = ()
data T_ParsesAtom_150
  = C_a'45'unit_176 | C_a'45'void_180 | C_a'45'int_184 |
    C_a'45'float_188 |
    C_a'45'eff_200 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                   AgdaAny AgdaAny T_ParsesAtom_150 T_ParsesAtom_150 |
    C_a'45'act_212 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                   AgdaAny AgdaAny T_ParsesAtom_150 T_ParsesAtom_150 |
    C_a'45'mu_220 AgdaAny T_ParsesFunSum_170 |
    C_a'45'nu_228 AgdaAny T_ParsesFunSum_170 |
    C_a'45'nu'45'act_236 AgdaAny T_ParsesFunSum_170 |
    C_a'45'extra_244 AgdaAny | C_a'45'paren_252 T_ParsesType_160
-- Once.Spec.Surface.Grammar.Types.ParsesProdTail
d_ParsesProdTail_152 a0 a1 a2 a3 a4 a5 a6 = ()
data T_ParsesProdTail_152
  = C_prod'45'done_270 |
    C_prod'45'star_284 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                       AgdaAny T_ParsesAtom_150 T_ParsesProdTail_152
-- Once.Spec.Surface.Grammar.Types.ParsesSumTail
d_ParsesSumTail_154 a0 a1 a2 a3 a4 a5 a6 = ()
data T_ParsesSumTail_154
  = C_sum'45'done_302 |
    C_sum'45'plus_316 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                      AgdaAny T_ParsesProd_156 T_ParsesSumTail_154
-- Once.Spec.Surface.Grammar.Types.ParsesProd
d_ParsesProd_156 a0 a1 a2 a3 a4 a5 = ()
data T_ParsesProd_156
  = C_prod_264 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
               AgdaAny T_ParsesAtom_150 T_ParsesProdTail_152
-- Once.Spec.Surface.Grammar.Types.ParsesSum
d_ParsesSum_158 a0 a1 a2 a3 a4 a5 = ()
data T_ParsesSum_158
  = C_sum_296 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
              AgdaAny T_ParsesProd_156 T_ParsesSumTail_154
-- Once.Spec.Surface.Grammar.Types.ParsesType
d_ParsesType_160 a0 a1 a2 a3 a4 a5 = ()
data T_ParsesType_160
  = C_type_328 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
               AgdaAny T_ParsesSum_158 T_ParsesArrowTail_162
-- Once.Spec.Surface.Grammar.Types.ParsesArrowTail
d_ParsesArrowTail_162 a0 a1 a2 a3 a4 a5 a6 = ()
data T_ParsesArrowTail_162
  = C_arrow'45'done_334 |
    C_arrow'45'grade_348 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                         AgdaAny T_GradeToken_24 T_ParsesType_160 |
    C_arrow_358 AgdaAny T_ParsesType_160
-- Once.Spec.Surface.Grammar.Types.ParsesFunAtom
d_ParsesFunAtom_164 a0 a1 a2 a3 a4 a5 = ()
data T_ParsesFunAtom_164
  = C_f'45'id_362 | C_f'45'k_370 AgdaAny T_ParsesAtom_150 |
    C_f'45'paren_378 T_ParsesFunSum_170
-- Once.Spec.Surface.Grammar.Types.ParsesFunProd
d_ParsesFunProd_166 a0 a1 a2 a3 a4 a5 = ()
data T_ParsesFunProd_166
  = C_fprod_390 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                AgdaAny T_ParsesFunAtom_164 T_ParsesFunProdTail_168
-- Once.Spec.Surface.Grammar.Types.ParsesFunProdTail
d_ParsesFunProdTail_168 a0 a1 a2 a3 a4 a5 a6 = ()
data T_ParsesFunProdTail_168
  = C_fprod'45'done_396 |
    C_fprod'45'star_410 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                        AgdaAny T_ParsesFunAtom_164 T_ParsesFunProdTail_168
-- Once.Spec.Surface.Grammar.Types.ParsesFunSum
d_ParsesFunSum_170 a0 a1 a2 a3 a4 a5 = ()
data T_ParsesFunSum_170
  = C_fsum_422 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
               AgdaAny T_ParsesFunProd_166 T_ParsesFunSumTail_172
-- Once.Spec.Surface.Grammar.Types.ParsesFunSumTail
d_ParsesFunSumTail_172 a0 a1 a2 a3 a4 a5 a6 = ()
data T_ParsesFunSumTail_172
  = C_fsum'45'done_428 |
    C_fsum'45'plus_442 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                       AgdaAny T_ParsesFunProd_166 T_ParsesFunSumTail_172
-- Once.Spec.Surface.Grammar.NoExtra
d_NoExtra_446 a0 a1 a2 a3 = ()
data T_NoExtra_446
-- Once.Spec.Surface.Grammar.lowerWord
d_lowerWord_450 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_lowerWord_450 v0
  = coe
      du_go_458
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Spec.Surface.Grammar._.go
d_go_458 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_go_458 ~v0 v1 = du_go_458 v1
du_go_458 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
du_go_458 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Char.d_primIsLower_8 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.TypeVar
d_TypeVar_462 a0 a1 a2 = ()
data T_TypeVar_462 = C_tvar_468
-- Once.Spec.Surface.Grammar.written
d_written_472 ::
  ([MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8] ->
   MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
   [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8] -> ()) ->
  T_TypeAlg_36
d_written_472 ~v0 = du_written_472
du_written_472 :: T_TypeAlg_36
du_written_472
  = coe
      C_constructor_106
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20)
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22)
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24)
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26)
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28)
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30)
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36)
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34)
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32
           (coe v1) (coe v0))
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38)
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 (coe v1) (coe v0))
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12)
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14)
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16)
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18)
-- Once.Spec.Surface.Grammar.ground
d_ground_486 :: T_TypeAlg_36
d_ground_486
  = coe
      C_constructor_106 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22)
      (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24)
      (\ v0 ->
         coe
           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
           (coe
              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
              (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44)))
      (\ v0 ->
         coe
           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
           (coe
              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
              (coe
                 MAlonzo.Code.Once.Spec.Grade.C_fin_42
                 (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))))
      (\ v0 v1 ->
         coe
           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
           (coe
              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v0)
              (coe
                 MAlonzo.Code.Once.Spec.Grade.C_fin_42
                 (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))))
      (coe MAlonzo.Code.Once.Spec.Type.C_μ_28)
      (\ v0 v1 ->
         coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v1) (coe v0))
      (coe MAlonzo.Code.Once.Spec.Type.C_K_38)
      (coe MAlonzo.Code.Once.Spec.Type.C_Id_40)
      (coe MAlonzo.Code.Once.Spec.Type.C__'8853'__42)
      (coe MAlonzo.Code.Once.Spec.Type.C__'8855'__44)
-- Once.Spec.Surface.Grammar.SigType.ParsesArrowTail
d_ParsesArrowTail_508 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesAtom
d_ParsesAtom_510 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesFunAtom
d_ParsesFunAtom_512 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesFunProd
d_ParsesFunProd_514 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesFunProdTail
d_ParsesFunProdTail_516 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesFunSum
d_ParsesFunSum_518 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesFunSumTail
d_ParsesFunSumTail_520 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesProd
d_ParsesProd_522 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesProdTail
d_ParsesProdTail_524 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesSum
d_ParsesSum_526 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesSumTail
d_ParsesSumTail_528 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.SigType.ParsesType
d_ParsesType_530 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesArrowTail
d_ParsesArrowTail_678 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesAtom
d_ParsesAtom_680 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesFunAtom
d_ParsesFunAtom_682 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesFunProd
d_ParsesFunProd_684 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesFunProdTail
d_ParsesFunProdTail_686 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesFunSum
d_ParsesFunSum_688 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesFunSumTail
d_ParsesFunSumTail_690 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesProd
d_ParsesProd_692 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesProdTail
d_ParsesProdTail_694 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesSum
d_ParsesSum_696 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesSumTail
d_ParsesSumTail_698 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.AliasType.ParsesType
d_ParsesType_700 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesArrowTail
d_ParsesArrowTail_848 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesAtom
d_ParsesAtom_850 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesFunAtom
d_ParsesFunAtom_852 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesFunProd
d_ParsesFunProd_854 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesFunProdTail
d_ParsesFunProdTail_856 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesFunSum
d_ParsesFunSum_858 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesFunSumTail
d_ParsesFunSumTail_860 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesProd
d_ParsesProd_862 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesProdTail
d_ParsesProdTail_864 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesSum
d_ParsesSum_866 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesSumTail
d_ParsesSumTail_868 a0 a1 a2 a3 = ()
-- Once.Spec.Surface.Grammar.Annot.ParsesType
d_ParsesType_870 a0 a1 a2 = ()
-- Once.Spec.Surface.Grammar.Reserved
d_Reserved_1016 a0 = ()
data T_Reserved_1016
  = C_r'45'in_1018 | C_r'45'of_1020 | C_r'45'let_1022 |
    C_r'45'destruct_1024 | C_r'45'Left_1026 | C_r'45'Right_1028
-- Once.Spec.Surface.Grammar.ArgStart
d_ArgStart_1030 a0 = ()
data T_ArgStart_1030
  = C_as'45'paren_1034 | C_as'45'lambda_1038 | C_as'45'int_1044 |
    C_as'45'float_1054 | C_as'45'word_1060
-- Once.Spec.Surface.Grammar.QualSuffix
d_QualSuffix_1062 a0 = ()
data T_QualSuffix_1062 = C_qual'45'suffix_1068
-- Once.Spec.Surface.Grammar.OpChar
d_OpChar_1070 a0 a1 = ()
data T_OpChar_1070
  = C_oc'45'dot_1072 | C_oc'45'plus_1074 | C_oc'45'minus_1076 |
    C_oc'45'star_1078 | C_oc'45'slash_1080 | C_oc'45'pct_1082 |
    C_oc'45'lt_1084 | C_oc'45'gt_1086 | C_oc'45'pipe_1088 |
    C_oc'45'amp_1090 | C_oc'45'at_1092
-- Once.Spec.Surface.Grammar.ParsesOpChars
d_ParsesOpChars_1094 a0 a1 a2 a3 = ()
data T_ParsesOpChars_1094
  = C_op'45'close_1102 |
    C_op'45'char_1116 MAlonzo.Code.Agda.Builtin.Char.T_Char_6
                      T_OpChar_1070 T_ParsesOpChars_1094
-- Once.Spec.Surface.Grammar.CompareToken
d_CompareToken_1118 a0 a1 = ()
data T_CompareToken_1118
  = C_ct'45'lt_1120 | C_ct'45'le_1122 | C_ct'45'gt_1124 |
    C_ct'45'ge_1126 | C_ct'45'eq_1128 | C_ct'45'ne_1130
-- Once.Spec.Surface.Grammar.AddToken
d_AddToken_1132 a0 a1 = ()
data T_AddToken_1132 = C_at'45'plus_1134 | C_at'45'minus_1136
-- Once.Spec.Surface.Grammar.MulToken
d_MulToken_1138 a0 a1 = ()
data T_MulToken_1138
  = C_mt'45'star_1140 | C_mt'45'slash_1142 | C_mt'45'pct_1144
-- Once.Spec.Surface.Grammar.ParsesExpr
d_ParsesExpr_1146 a0 a1 a2 = ()
data T_ParsesExpr_1146
  = C_expr_1182 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 T_ParsesCmp_1150
                T_ParsesCompTail_1148
-- Once.Spec.Surface.Grammar.ParsesCompTail
d_ParsesCompTail_1148 a0 a1 a2 a3 = ()
data T_ParsesCompTail_1148
  = C_comp'45'done_1188 |
    C_comp'45'dot_1202 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                       MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 T_ParsesCmp_1150
                       T_ParsesCompTail_1148
-- Once.Spec.Surface.Grammar.ParsesCmp
d_ParsesCmp_1150 a0 a1 a2 = ()
data T_ParsesCmp_1150
  = C_cmp'45'none_1214 T_ParsesAdd_1152 |
    C_cmp_1230 MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8
               [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
               T_CompareToken_1118 T_ParsesAdd_1152 T_ParsesAdd_1152
-- Once.Spec.Surface.Grammar.ParsesAdd
d_ParsesAdd_1152 a0 a1 a2 = ()
data T_ParsesAdd_1152
  = C_add_1242 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
               MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 T_ParsesMul_1156
               T_ParsesAddTail_1154
-- Once.Spec.Surface.Grammar.ParsesAddTail
d_ParsesAddTail_1154 a0 a1 a2 a3 = ()
data T_ParsesAddTail_1154
  = C_add'45'done_1252 |
    C_add'45'op_1270 MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44
                     [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                     MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 T_AddToken_1132
                     T_ParsesMul_1156 T_ParsesAddTail_1154
-- Once.Spec.Surface.Grammar.ParsesMul
d_ParsesMul_1156 a0 a1 a2 = ()
data T_ParsesMul_1156
  = C_mul_1282 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
               MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 T_ParsesUnary_1160
               T_ParsesMulTail_1158
-- Once.Spec.Surface.Grammar.ParsesMulTail
d_ParsesMulTail_1158 a0 a1 a2 a3 = ()
data T_ParsesMulTail_1158
  = C_mul'45'done_1292 |
    C_mul'45'op_1310 MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44
                     [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                     MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 T_MulToken_1138
                     T_ParsesUnary_1160 T_ParsesMulTail_1158
-- Once.Spec.Surface.Grammar.ParsesUnary
d_ParsesUnary_1160 a0 a1 a2 = ()
data T_ParsesUnary_1160
  = C_neg_1318 T_ParsesUnary_1160 | C_unary_1326 T_ParsesApp_1162
-- Once.Spec.Surface.Grammar.ParsesApp
d_ParsesApp_1162 a0 a1 a2 = ()
data T_ParsesApp_1162
  = C_app_1338 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
               MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
               T_ParsesAtomExpr_1166 T_ParsesAppTail_1164
-- Once.Spec.Surface.Grammar.ParsesAppTail
d_ParsesAppTail_1164 a0 a1 a2 a3 = ()
data T_ParsesAppTail_1164
  = C_app'45'done_1344 |
    C_app'45'arg_1358 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                      MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 T_ArgStart_1030
                      T_ParsesAtomExpr_1166 T_ParsesAppTail_1164
-- Once.Spec.Surface.Grammar.ParsesAtomExpr
d_ParsesAtomExpr_1166 a0 a1 a2 = ()
data T_ParsesAtomExpr_1166
  = C_atom'45'unit_1362 | C_atom'45'int_1368 | C_atom'45'float_1378 |
    C_atom'45'var_1384 | C_atom'45'qual_1392 |
    C_atom'45'paren_1404 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                         MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 T_ParsesExpr_1146
                         T_ParsesParenCont_1170 |
    C_atom'45'op_1412 T_ParsesOpChars_1094 |
    C_atom'45'lambda_1420 T_ParsesLamParams_1168 |
    C_atom'45'let_1434 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                       T_ParsesExpr_1146 T_ParsesExpr_1146 |
    C_atom'45'destruct_1454 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                            [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8] T_ParsesExpr_1146
                            T_ParsesExpr_1146 T_ParsesExpr_1146
-- Once.Spec.Surface.Grammar.ParsesLamParams
d_ParsesLamParams_1168 a0 a1 a2 = ()
data T_ParsesLamParams_1168
  = C_lam'45'body_1462 T_ParsesExpr_1146 |
    C_lam'45'arg_1472 T_ParsesLamParams_1168
-- Once.Spec.Surface.Grammar.ParsesParenCont
d_ParsesParenCont_1170 a0 a1 a2 a3 = ()
data T_ParsesParenCont_1170
  = C_paren'45'close_1478 | C_paren'45'pair_1488 T_ParsesExpr_1146 |
    C_paren'45'annot_1498 T_ParsesType_160
-- Once.Spec.Surface.Grammar.wrapLams
d_wrapLams_1500 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_wrapLams_1500 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 (coe v2)
             (coe d_wrapLams_1500 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Grammar.ParsesParams
d_ParsesParams_1510 a0 a1 a2 = ()
data T_ParsesParams_1510
  = C_params'45'eq_1516 T_Starts_8 |
    C_params'45'cons_1526 T_StartsWord_16 T_ParsesParams_1510 |
    C_params'45'stop_1532 | C_params'45'none_1536
-- Once.Spec.Surface.Grammar.ParsesFunDef
d_ParsesFunDef_1540 a0 a1 a2 a3 = ()
data T_ParsesFunDef_1540
  = C_fundef_1554 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 T_ParsesParams_1510
                  T_ParsesExpr_1146
-- Once.Spec.Surface.Grammar.ParsesModulePath
d_ParsesModulePath_1556 a0 a1 a2 = ()
data T_ParsesModulePath_1556
  = C_path'45'cons_1566 T_ParsesModulePath_1556 |
    C_path'45'dotstop_1572 | C_path'45'end_1578
-- Once.Spec.Surface.Grammar.ParsesImport
d_ParsesImport_1580 a0 a1 a2 = ()
data T_ParsesImport_1580
  = C_import'45'as_1590 T_ParsesModulePath_1556 |
    C_import'45'plain_1598 T_ParsesModulePath_1556
-- Once.Spec.Surface.Grammar.ParsesTypeAlias
d_ParsesTypeAlias_1602 a0 a1 a2 a3 a4 = ()
data T_ParsesTypeAlias_1602
  = C_alias'45'eq_1614 T_ParsesType_160 |
    C_alias'45'param_1626 T_ParsesTypeAlias_1602
-- Once.Spec.Surface.Grammar.ParsesOpAfter
d_ParsesOpAfter_1630 a0 a1 a2 a3 = ()
data T_ParsesOpAfter_1630
  = C_op'45'sig_1640 T_ParsesType_160 |
    C_op'45'def_1648 T_ParsesFunDef_1540
-- Once.Spec.Surface.Grammar.NotKeyword
d_NotKeyword_1650 a0 = ()
data T_NotKeyword_1650 = C_not'45'keyword_1654
-- Once.Spec.Surface.Grammar.ParsesDecl
d_ParsesDecl_1656 a0 a1 a2 = ()
data T_ParsesDecl_1656
  = C_decl'45'import_1664 T_ParsesImport_1580 |
    C_decl'45'alias_1674 T_ParsesTypeAlias_1602 |
    C_decl'45'signature_1684 T_ParsesType_160 |
    C_decl'45'typesig_1694 T_NotKeyword_1650 T_ParsesType_160 |
    C_decl'45'fundef_1704 T_NotKeyword_1650 T_ParsesFunDef_1540 |
    C_decl'45'op_1716 MAlonzo.Code.Agda.Builtin.String.T_String_6
                      [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                      T_ParsesOpChars_1094 T_ParsesOpAfter_1630
-- Once.Spec.Surface.Grammar.SkipNewlines
d_SkipNewlines_1718 a0 a1 = ()
data T_SkipNewlines_1718
  = C_skip'45'nl_1724 T_SkipNewlines_1718 | C_skip'45'done_1728
-- Once.Spec.Surface.Grammar.ParsesDecls
d_ParsesDecls_1730 a0 a1 a2 = ()
data T_ParsesDecls_1730
  = C_decls'45'stop_1740 T_SkipNewlines_1718 |
    C_decls'45'cons_1754 [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                         [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
                         T_SkipNewlines_1718 T_ParsesDecl_1656 T_ParsesDecls_1730
-- Once.Spec.Surface.Grammar.Trailing
d_Trailing_1756 a0 = ()
data T_Trailing_1756
  = C_trail'45'nl_1760 T_Trailing_1756 | C_trail'45'eof_1762
-- Once.Spec.Surface.Grammar.Parses
d_Parses_1764 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 -> ()
d_Parses_1764 = erased
