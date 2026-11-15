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

module MAlonzo.Code.Once.Parser.ExprRelation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.ExprRelation.isReserved
d_isReserved_6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isReserved_6 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
         (coe
            MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
            (coe ("in" :: Data.Text.Text))))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
            (coe
               MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
               (coe ("of" :: Data.Text.Text))))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe
               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
               (coe
                  MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                  (coe ("let" :: Data.Text.Text))))
            (coe
               MAlonzo.Code.Data.Bool.Base.d__'8744'__30
               (coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                  (coe
                     MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                     (coe ("destruct" :: Data.Text.Text))))
               (coe
                  MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                  (coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                        (coe ("Left" :: Data.Text.Text))))
                  (coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                        (coe ("Right" :: Data.Text.Text))))))))
-- Once.Parser.ExprRelation.NotDot
d_NotDot_10 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotDot_10 = erased
-- Once.Parser.ExprRelation.NotAdd
d_NotAdd_12 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotAdd_12 = erased
-- Once.Parser.ExprRelation.NotMul
d_NotMul_14 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotMul_14 = erased
-- Once.Parser.ExprRelation.NotCmp
d_NotCmp_16 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotCmp_16 = erased
-- Once.Parser.ExprRelation.NotNumeral
d_NotNumeral_18 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotNumeral_18 = erased
-- Once.Parser.ExprRelation.OneCharGlyph
d_OneCharGlyph_20 a0 a1 = ()
data T_OneCharGlyph_20
  = C_ocg'45''43'_22 | C_ocg'45''45'_24 | C_ocg'45''42'_26 |
    C_ocg'45''47'_28 | C_ocg'45''60'_30 | C_ocg'45''62'_32
-- Once.Parser.ExprRelation.NotAtomStart
d_NotAtomStart_34 a0 = ()
data T_NotAtomStart_34
  = C_nas'45''91''93'_36 | C_nas'45'word'45'res_42 |
    C_nas'45'TRParen_46 | C_nas'45'TLBrace_50 | C_nas'45'TRBrace_54 |
    C_nas'45'TColon_58 | C_nas'45'TEquals_62 | C_nas'45'TArrow_66 |
    C_nas'45'TCaret0_70 | C_nas'45'TCaret1_74 | C_nas'45'TCaretW_78 |
    C_nas'45'TComma_82 | C_nas'45'TSemicolon_86 | C_nas'45'TAt_90 |
    C_nas'45'TPipe_94 | C_nas'45'TDot_98 | C_nas'45'TPlus_102 |
    C_nas'45'TMinus_106 | C_nas'45'TStar_110 | C_nas'45'TSlash_114 |
    C_nas'45'TPercent_118 | C_nas'45'TAmpersand_122 |
    C_nas'45'TLt_126 | C_nas'45'TLe_130 | C_nas'45'TGt_134 |
    C_nas'45'TGe_138 | C_nas'45'TEqEq_142 | C_nas'45'TNeq_146 |
    C_nas'45'TOpD_152 | C_nas'45'TBang_156 | C_nas'45'TNewline_160 |
    C_nas'45'TEOF_164
-- Once.Parser.ExprRelation.AppArgOk
d_AppArgOk_166 a0 = ()
data T_AppArgOk_166
  = C_aao'45'TLParen_170 | C_aao'45'TLambda_174 | C_aao'45'TInt_182 |
    C_aao'45'TFloat_194 | C_aao'45'word_200
-- Once.Parser.ExprRelation.NotTWord
d_NotTWord_202 a0 = ()
data T_NotTWord_202
  = C_ntw'45'TLParen_204 | C_ntw'45'TRParen_206 |
    C_ntw'45'TLBrace_208 | C_ntw'45'TRBrace_210 | C_ntw'45'TColon_212 |
    C_ntw'45'TEquals_214 | C_ntw'45'TArrow_216 | C_ntw'45'TCaret0_218 |
    C_ntw'45'TCaret1_220 | C_ntw'45'TCaretW_222 |
    C_ntw'45'TLambda_224 | C_ntw'45'TComma_226 |
    C_ntw'45'TSemicolon_228 | C_ntw'45'TAt_230 | C_ntw'45'TPipe_232 |
    C_ntw'45'TDot_234 | C_ntw'45'TPlus_236 | C_ntw'45'TMinus_238 |
    C_ntw'45'TStar_240 | C_ntw'45'TSlash_242 | C_ntw'45'TPercent_244 |
    C_ntw'45'TAmpersand_246 | C_ntw'45'TLt_248 | C_ntw'45'TLe_250 |
    C_ntw'45'TGt_252 | C_ntw'45'TGe_254 | C_ntw'45'TEqEq_256 |
    C_ntw'45'TNeq_258 | C_ntw'45'TBang_260 | C_ntw'45'TNewline_262 |
    C_ntw'45'TEOF_264 | C_ntw'45'TOpD_268 | C_ntw'45'TInt_274 |
    C_ntw'45'TFloat_284 | C_ntw'45'TString_288
-- Once.Parser.ExprRelation.NotQualPrefix
d_NotQualPrefix_290 a0 = ()
data T_NotQualPrefix_290
  = C_nqp'45''91''93'_292 | C_nqp'45'TLParen_296 |
    C_nqp'45'TRParen_300 | C_nqp'45'TLBrace_304 |
    C_nqp'45'TRBrace_308 | C_nqp'45'TColon_312 | C_nqp'45'TEquals_316 |
    C_nqp'45'TArrow_320 | C_nqp'45'TCaret0_324 | C_nqp'45'TCaret1_328 |
    C_nqp'45'TCaretW_332 | C_nqp'45'TLambda_336 | C_nqp'45'TComma_340 |
    C_nqp'45'TSemicolon_344 | C_nqp'45'TPipe_348 | C_nqp'45'TDot_352 |
    C_nqp'45'TPlus_356 | C_nqp'45'TMinus_360 | C_nqp'45'TStar_364 |
    C_nqp'45'TSlash_368 | C_nqp'45'TPercent_372 |
    C_nqp'45'TAmpersand_376 | C_nqp'45'TLt_380 | C_nqp'45'TLe_384 |
    C_nqp'45'TGt_388 | C_nqp'45'TGe_392 | C_nqp'45'TEqEq_396 |
    C_nqp'45'TNeq_400 | C_nqp'45'TBang_404 | C_nqp'45'TNewline_408 |
    C_nqp'45'TEOF_412 | C_nqp'45'TOpD_418 | C_nqp'45'TWord_424 |
    C_nqp'45'TInt_432 | C_nqp'45'TFloat_444 | C_nqp'45'TString_450 |
    C_nqp'45'TAt'45''91''93'_452 |
    C_nqp'45'TAt'45'cons_458 T_NotTWord_202
-- Once.Parser.ExprRelation.ReservedView
d_ReservedView_462 a0 = ()
data T_ReservedView_462
  = C_rv'45'reserved_466 | C_rv'45'not'45'reserved_468
-- Once.Parser.ExprRelation.reserved-view
d_reserved'45'view_472 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_ReservedView_462
d_reserved'45'view_472 v0
  = let v1
          = MAlonzo.Code.Data.Bool.Base.d__'8744'__30
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (\ v1 ->
                       coe
                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                         (coe v0))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                       (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                       (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          ("in" :: Data.Text.Text)))))
              (coe
                 MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                    (coe
                       MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                       (coe ("of" :: Data.Text.Text))))
                 (coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                       (coe
                          MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                          (coe ("let" :: Data.Text.Text))))
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                          (coe
                             MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                             (coe ("destruct" :: Data.Text.Text))))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                             (coe
                                MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                                (coe ("Left" :: Data.Text.Text))))
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                             (coe
                                MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                                (coe ("Right" :: Data.Text.Text)))))))) in
    coe
      (if coe v1
         then coe C_rv'45'reserved_466
         else coe C_rv'45'not'45'reserved_468)
-- Once.Parser.ExprRelation.WordEqView
d_WordEqView_490 a0 a1 = ()
data T_WordEqView_490 = C_we'45'match_496 | C_we'45'nomatch_498
-- Once.Parser.ExprRelation.wordEq-view
d_wordEq'45'view_504 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_WordEqView_490
d_wordEq'45'view_504 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe seq (coe v4) (coe C_we'45'match_496)
                else coe seq (coe v4) (coe C_we'45'nomatch_498)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.ExprRelation.ParsesExpr
d_ParsesExpr_526 a0 a1 a2 = ()
newtype T_ParsesExpr_526 = C_pe'45'mk_576 T_ParsesComp_528
-- Once.Parser.ExprRelation.ParsesComp
d_ParsesComp_528 a0 a1 a2 = ()
data T_ParsesComp_528
  = C_pc'45'mk_588 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesCmp_532
                   T_ParsesCompTail_530
-- Once.Parser.ExprRelation.ParsesCompTail
d_ParsesCompTail_530 a0 a1 a2 a3 = ()
data T_ParsesCompTail_530
  = C_pct'45'done_594 AgdaAny |
    C_pct'45'dot_608 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesCmp_532
                     T_ParsesCompTail_530
-- Once.Parser.ExprRelation.ParsesCmp
d_ParsesCmp_532 a0 a1 a2 = ()
data T_ParsesCmp_532
  = C_pcm'45'noop_616 T_ParsesAdd_534 AgdaAny |
    C_pcm'45'lt_628 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_534 T_ParsesAdd_534 |
    C_pcm'45'le_640 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_534 T_ParsesAdd_534 |
    C_pcm'45'gt_652 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_534 T_ParsesAdd_534 |
    C_pcm'45'ge_664 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_534 T_ParsesAdd_534 |
    C_pcm'45'eq_676 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_534 T_ParsesAdd_534 |
    C_pcm'45'ne_688 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_534 T_ParsesAdd_534 |
    C_pcm'45'dot_702 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     T_ParsesAdd_534 T_ParsesAdd_534
-- Once.Parser.ExprRelation.ParsesAdd
d_ParsesAdd_534 a0 a1 a2 = ()
data T_ParsesAdd_534
  = C_pa'45'mk_714 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesMul_538
                   T_ParsesAddTail_536
-- Once.Parser.ExprRelation.ParsesAddTail
d_ParsesAddTail_536 a0 a1 a2 a3 = ()
data T_ParsesAddTail_536
  = C_pat'45'done_720 AgdaAny |
    C_pat'45'plus_734 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesMul_538
                      T_ParsesAddTail_536 |
    C_pat'45'minus_748 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesMul_538
                       T_ParsesAddTail_536 |
    C_pat'45'dot_764 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesMul_538
                     T_ParsesAddTail_536
-- Once.Parser.ExprRelation.ParsesMul
d_ParsesMul_538 a0 a1 a2 = ()
data T_ParsesMul_538
  = C_pm'45'mk_776 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesUnary_542
                   T_ParsesMulTail_540
-- Once.Parser.ExprRelation.ParsesMulTail
d_ParsesMulTail_540 a0 a1 a2 a3 = ()
data T_ParsesMulTail_540
  = C_pmt'45'done_782 AgdaAny |
    C_pmt'45'star_796 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesUnary_542
                      T_ParsesMulTail_540 |
    C_pmt'45'slash_810 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesUnary_542
                       T_ParsesMulTail_540 |
    C_pmt'45'percent_824 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                         MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesUnary_542
                         T_ParsesMulTail_540 |
    C_pmt'45'dot_840 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesUnary_542
                     T_ParsesMulTail_540
-- Once.Parser.ExprRelation.ParsesUnary
d_ParsesUnary_542 a0 a1 a2 = ()
data T_ParsesUnary_542
  = C_pu'45'neg_848 AgdaAny T_ParsesUnary_542 |
    C_pu'45'neg'45'int_860 T_ParsesAppTail_546 |
    C_pu'45'neg'45'float_876 T_ParsesAppTail_546 |
    C_pu'45'app_884 T_ParsesApp_544
-- Once.Parser.ExprRelation.ParsesApp
d_ParsesApp_544 a0 a1 a2 = ()
data T_ParsesApp_544
  = C_papp'45'mk_896 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44
                     T_ParsesAtomExpr_548 T_ParsesAppTail_546
-- Once.Parser.ExprRelation.ParsesAppTail
d_ParsesAppTail_546 a0 a1 a2 a3 = ()
data T_ParsesAppTail_546
  = C_papp'45'done_902 T_NotAtomStart_34 |
    C_papp'45'arg_916 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_AppArgOk_166
                      T_ParsesAtomExpr_548 T_ParsesAppTail_546
-- Once.Parser.ExprRelation.ParsesAtomExpr
d_ParsesAtomExpr_548 a0 a1 a2 = ()
data T_ParsesAtomExpr_548
  = C_pae'45'unit_920 | C_pae'45'int_928 | C_pae'45'float_940 |
    C_pae'45'var_946 T_NotQualPrefix_290 | C_pae'45'qual_954 |
    C_pae'45'paren_966 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesExpr_526
                       T_ParsesParenCont_566 |
    C_pae'45'lambda_974 T_ParsesLamParams_550 |
    C_pae'45'let_982 T_ParsesLet_552 |
    C_pae'45'destruct_990 T_ParsesDestruct_556 |
    C_pae'45'paren'45'op_998 T_ParsesOpExpr_564
-- Once.Parser.ExprRelation.ParsesLamParams
d_ParsesLamParams_550 a0 a1 a2 = ()
data T_ParsesLamParams_550
  = C_plp'45'body_1006 T_ParsesExpr_526 |
    C_plp'45'arg_1016 T_ParsesLamParams_550
-- Once.Parser.ExprRelation.ParsesLet
d_ParsesLet_552 a0 a1 a2 = ()
data T_ParsesLet_552
  = C_plet'45'single_1030 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                          MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesExpr_526
                          T_ParsesLetIn_554
-- Once.Parser.ExprRelation.ParsesLetIn
d_ParsesLetIn_554 a0 a1 a2 a3 a4 = ()
newtype T_ParsesLetIn_554 = C_plin_1042 T_ParsesExpr_526
-- Once.Parser.ExprRelation.ParsesDestruct
d_ParsesDestruct_556 a0 a1 a2 = ()
data T_ParsesDestruct_556
  = C_pd'45'mk_1054 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesExpr_526
                    T_ParsesDestructOf_558
-- Once.Parser.ExprRelation.ParsesDestructOf
d_ParsesDestructOf_558 a0 a1 a2 a3 = ()
newtype T_ParsesDestructOf_558
  = C_pdof_1064 T_ParsesDestructBranches_560
-- Once.Parser.ExprRelation.ParsesDestructBranches
d_ParsesDestructBranches_560 a0 a1 a2 a3 = ()
data T_ParsesDestructBranches_560
  = C_pdb_1080 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
               MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 T_ParsesExpr_526
               T_ParsesRightBranch_562
-- Once.Parser.ExprRelation.ParsesRightBranch
d_ParsesRightBranch_562 a0 a1 a2 a3 a4 a5 = ()
newtype T_ParsesRightBranch_562 = C_prb_1096 T_ParsesExpr_526
-- Once.Parser.ExprRelation.ParsesOpExpr
d_ParsesOpExpr_564 a0 a1 a2 a3 = ()
data T_ParsesOpExpr_564
  = C_poe'45'close_1104 | C_poe'45'dot_1114 T_ParsesOpExpr_564 |
    C_poe'45'plus_1124 T_ParsesOpExpr_564 |
    C_poe'45'minus_1134 T_ParsesOpExpr_564 |
    C_poe'45'star_1144 T_ParsesOpExpr_564 |
    C_poe'45'slash_1154 T_ParsesOpExpr_564 |
    C_poe'45'percent_1164 T_ParsesOpExpr_564 |
    C_poe'45'lt_1174 T_ParsesOpExpr_564 |
    C_poe'45'gt_1184 T_ParsesOpExpr_564 |
    C_poe'45'pipe_1194 T_ParsesOpExpr_564 |
    C_poe'45'amp_1204 T_ParsesOpExpr_564 |
    C_poe'45'at_1214 T_ParsesOpExpr_564 |
    C_poe'45'dotted_1228 MAlonzo.Code.Agda.Builtin.Char.T_Char_6
                         T_OneCharGlyph_20 T_ParsesOpExpr_564
-- Once.Parser.ExprRelation.ParsesParenCont
d_ParsesParenCont_566 a0 a1 a2 a3 = ()
data T_ParsesParenCont_566
  = C_ppc'45'close_1234 |
    C_ppc'45'pair_1246 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       T_ParsesExpr_526 T_ParsesParenTriple_568 |
    C_ppc'45'annot_1256 MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
-- Once.Parser.ExprRelation.ParsesParenTriple
d_ParsesParenTriple_568 a0 a1 a2 a3 = ()
data T_ParsesParenTriple_568 = C_ppt'45'close_1264
-- Once.Parser.ExprRelation.ParsesExpr-shrinks
d_ParsesExpr'45'shrinks_1272 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesExpr_526 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesExpr'45'shrinks_1272 v0 ~v1 ~v2 v3
  = du_ParsesExpr'45'shrinks_1272 v0 v3
du_ParsesExpr'45'shrinks_1272 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesExpr_526 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesExpr'45'shrinks_1272 v0 v1
  = case coe v1 of
      C_pe'45'mk_576 v5
        -> coe du_ParsesComp'45'shrinks_1280 (coe v0) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesComp-shrinks
d_ParsesComp'45'shrinks_1280 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesComp_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesComp'45'shrinks_1280 v0 ~v1 ~v2 v3
  = du_ParsesComp'45'shrinks_1280 v0 v3
du_ParsesComp'45'shrinks_1280 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesComp_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesComp'45'shrinks_1280 v0 v1
  = case coe v1 of
      C_pc'45'mk_588 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesCompTail'45'shrinks_1290 (coe v3) (coe v8))
             (coe du_ParsesCmp'45'shrinks_1298 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesCompTail-shrinks
d_ParsesCompTail'45'shrinks_1290 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCompTail_530 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesCompTail'45'shrinks_1290 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesCompTail'45'shrinks_1290 v1 v4
du_ParsesCompTail'45'shrinks_1290 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCompTail_530 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesCompTail'45'shrinks_1290 v0 v1
  = case coe v1 of
      C_pct'45'done_594 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pct'45'dot_608 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesCompTail'45'shrinks_1290 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesCmp'45'shrinks_1298 (coe v11) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesCmp-shrinks
d_ParsesCmp'45'shrinks_1298 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCmp_532 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesCmp'45'shrinks_1298 v0 ~v1 ~v2 v3
  = du_ParsesCmp'45'shrinks_1298 v0 v3
du_ParsesCmp'45'shrinks_1298 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCmp_532 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesCmp'45'shrinks_1298 v0 v1
  = case coe v1 of
      C_pcm'45'noop_616 v5 v6
        -> coe du_ParsesAdd'45'shrinks_1306 (coe v0) (coe v5)
      C_pcm'45'lt_628 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1306 (coe v3) (coe v8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                (coe
                   addInt (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                      (coe (0 :: Integer)) (coe v3)))
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                         (coe (0 :: Integer)) (coe v3))))
                (coe du_ParsesAdd'45'shrinks_1306 (coe v0) (coe v7)))
      C_pcm'45'le_640 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1306 (coe v3) (coe v8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                (coe
                   addInt (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                      (coe (0 :: Integer)) (coe v3)))
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                         (coe (0 :: Integer)) (coe v3))))
                (coe du_ParsesAdd'45'shrinks_1306 (coe v0) (coe v7)))
      C_pcm'45'gt_652 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1306 (coe v3) (coe v8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                (coe
                   addInt (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                      (coe (0 :: Integer)) (coe v3)))
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                         (coe (0 :: Integer)) (coe v3))))
                (coe du_ParsesAdd'45'shrinks_1306 (coe v0) (coe v7)))
      C_pcm'45'ge_664 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1306 (coe v3) (coe v8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                (coe
                   addInt (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                      (coe (0 :: Integer)) (coe v3)))
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                         (coe (0 :: Integer)) (coe v3))))
                (coe du_ParsesAdd'45'shrinks_1306 (coe v0) (coe v7)))
      C_pcm'45'eq_676 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1306 (coe v3) (coe v8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                (coe
                   addInt (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                      (coe (0 :: Integer)) (coe v3)))
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                         (coe (0 :: Integer)) (coe v3))))
                (coe du_ParsesAdd'45'shrinks_1306 (coe v0) (coe v7)))
      C_pcm'45'ne_688 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1306 (coe v3) (coe v8))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                (coe
                   addInt (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                      (coe (0 :: Integer)) (coe v3)))
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                         (coe (0 :: Integer)) (coe v3))))
                (coe du_ParsesAdd'45'shrinks_1306 (coe v0) (coe v7)))
      C_pcm'45'dot_702 v4 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v4)
             (coe du_ParsesAdd'45'shrinks_1306 (coe v4) (coe v10))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                (coe
                   addInt (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (coe (\ v11 v12 -> addInt (coe (1 :: Integer)) (coe v12)))
                      (coe (0 :: Integer)) (coe v4)))
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (coe (\ v11 v12 -> addInt (coe (1 :: Integer)) (coe v12)))
                         (coe (0 :: Integer)) (coe v4))))
                (coe du_ParsesAdd'45'shrinks_1306 (coe v0) (coe v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAdd-shrinks
d_ParsesAdd'45'shrinks_1306 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAdd_534 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAdd'45'shrinks_1306 v0 ~v1 ~v2 v3
  = du_ParsesAdd'45'shrinks_1306 v0 v3
du_ParsesAdd'45'shrinks_1306 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAdd_534 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAdd'45'shrinks_1306 v0 v1
  = case coe v1 of
      C_pa'45'mk_714 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesAddTail'45'shrinks_1316 (coe v3) (coe v8))
             (coe du_ParsesMul'45'shrinks_1324 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAddTail-shrinks
d_ParsesAddTail'45'shrinks_1316 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAddTail_536 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAddTail'45'shrinks_1316 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesAddTail'45'shrinks_1316 v1 v4
du_ParsesAddTail'45'shrinks_1316 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAddTail_536 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAddTail'45'shrinks_1316 v0 v1
  = case coe v1 of
      C_pat'45'done_720 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pat'45'plus_734 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1316 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesMul'45'shrinks_1324 (coe v11) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pat'45'minus_748 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1316 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesMul'45'shrinks_1324 (coe v11) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pat'45'dot_764 v5 v7 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1316 (coe v5) (coe v11))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v13)
                          (coe du_ParsesMul'45'shrinks_1324 (coe v13) (coe v10))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v14 = \ v14 -> addInt (coe (1 :: Integer)) (coe v14) in
                                    coe (coe (\ v15 -> v14)))
                                   (coe (0 :: Integer)) (coe v13))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesMul-shrinks
d_ParsesMul'45'shrinks_1324 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMul_538 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesMul'45'shrinks_1324 v0 ~v1 ~v2 v3
  = du_ParsesMul'45'shrinks_1324 v0 v3
du_ParsesMul'45'shrinks_1324 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMul_538 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesMul'45'shrinks_1324 v0 v1
  = case coe v1 of
      C_pm'45'mk_776 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesMulTail'45'shrinks_1334 (coe v3) (coe v8))
             (coe du_ParsesUnary'45'shrinks_1342 (coe v0) (coe v5) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesMulTail-shrinks
d_ParsesMulTail'45'shrinks_1334 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMulTail_540 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesMulTail'45'shrinks_1334 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesMulTail'45'shrinks_1334 v1 v4
du_ParsesMulTail'45'shrinks_1334 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMulTail_540 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesMulTail'45'shrinks_1334 v0 v1
  = case coe v1 of
      C_pmt'45'done_782 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pmt'45'star_796 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1334 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1342 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'slash_810 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1334 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1342 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'percent_824 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1334 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1342 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'dot_840 v5 v7 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1334 (coe v5) (coe v11))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v13)
                          (coe du_ParsesUnary'45'shrinks_1342 (coe v13) (coe v7) (coe v10))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v14 = \ v14 -> addInt (coe (1 :: Integer)) (coe v14) in
                                    coe (coe (\ v15 -> v14)))
                                   (coe (0 :: Integer)) (coe v13))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesUnary-shrinks
d_ParsesUnary'45'shrinks_1342 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesUnary_542 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesUnary'45'shrinks_1342 v0 v1 ~v2 v3
  = du_ParsesUnary'45'shrinks_1342 v0 v1 v3
du_ParsesUnary'45'shrinks_1342 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_ParsesUnary_542 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesUnary'45'shrinks_1342 v0 v1 v2
  = case coe v2 of
      C_pu'45'neg_848 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_72 v10
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                           (coe du_ParsesUnary'45'shrinks_1342 (coe v9) (coe v10) (coe v7))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (let v11 = \ v11 -> addInt (coe (1 :: Integer)) (coe v11) in
                                     coe (coe (\ v12 -> v11)))
                                    (coe (0 :: Integer)) (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pu'45'neg'45'int_860 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                           (coe du_ParsesAppTail'45'shrinks_1360 (coe v12) (coe v8))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                              (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                     coe (coe (\ v14 -> v13)))
                                    (coe (0 :: Integer)) (coe v12))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pu'45'neg'45'float_876 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v12 of
                    (:) v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                           (coe du_ParsesAppTail'45'shrinks_1360 (coe v14) (coe v10))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                              (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (let v15 = \ v15 -> addInt (coe (1 :: Integer)) (coe v15) in
                                     coe (coe (\ v16 -> v15)))
                                    (coe (0 :: Integer)) (coe v14))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pu'45'app_884 v6
        -> coe du_ParsesApp'45'shrinks_1350 (coe v0) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesApp-shrinks
d_ParsesApp'45'shrinks_1350 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesApp_544 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesApp'45'shrinks_1350 v0 ~v1 ~v2 v3
  = du_ParsesApp'45'shrinks_1350 v0 v3
du_ParsesApp'45'shrinks_1350 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesApp_544 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesApp'45'shrinks_1350 v0 v1
  = case coe v1 of
      C_papp'45'mk_896 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesAppTail'45'shrinks_1360 (coe v3) (coe v8))
             (coe
                d_ParsesAtomExpr'45'shrinks_1368 (coe v0) (coe v5) (coe v3)
                (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAppTail-shrinks
d_ParsesAppTail'45'shrinks_1360 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAppTail_546 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAppTail'45'shrinks_1360 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesAppTail'45'shrinks_1360 v1 v4
du_ParsesAppTail'45'shrinks_1360 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAppTail_546 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAppTail'45'shrinks_1360 v0 v1
  = case coe v1 of
      C_papp'45'done_902 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_papp'45'arg_916 v4 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe du_ParsesAppTail'45'shrinks_1360 (coe v4) (coe v10))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                (coe
                   d_ParsesAtomExpr'45'shrinks_1368 (coe v0) (coe v6) (coe v4)
                   (coe v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAtomExpr-shrinks
d_ParsesAtomExpr'45'shrinks_1368 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAtomExpr_548 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAtomExpr'45'shrinks_1368 v0 v1 v2 v3
  = case coe v3 of
      C_pae'45'unit_920
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'int_928
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v7 = \ v7 -> addInt (coe (1 :: Integer)) (coe v7) in
                    coe (coe (\ v8 -> v7)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'float_940
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v9 = \ v9 -> addInt (coe (1 :: Integer)) (coe v9) in
                    coe (coe (\ v10 -> v9)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'var_946 v7
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                    coe (coe (\ v9 -> v8)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'qual_954
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                    coe (coe (\ v9 -> v8)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'paren_966 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
                    (coe
                       du_ParsesParenCont'45'shrinks_1458 (coe v5) (coe v1) (coe v2)
                       (coe v10))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                       (coe du_ParsesExpr'45'shrinks_1272 (coe v12) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                 coe (coe (\ v14 -> v13)))
                                (coe (0 :: Integer)) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'lambda_974 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesLamParams'45'shrinks_1386 (coe v9) (coe v1) (coe v2)
                       (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'let_982 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesLet'45'shrinks_1394 (coe v9) (coe v1) (coe v2) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'destruct_990 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesDestruct'45'shrinks_1414 (coe v9) (coe v1) (coe v2)
                       (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'paren'45'op_998 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v2) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesOpExpr-shrinks
d_ParsesOpExpr'45'shrinks_1378 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesOpExpr_564 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesOpExpr'45'shrinks_1378 ~v0 v1 ~v2 v3 v4
  = du_ParsesOpExpr'45'shrinks_1378 v1 v3 v4
du_ParsesOpExpr'45'shrinks_1378 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesOpExpr_564 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesOpExpr'45'shrinks_1378 v0 v1 v2
  = case coe v2 of
      C_poe'45'close_1104
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v1)))
      C_poe'45'dot_1114 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'plus_1124 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'minus_1134 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'star_1144 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'slash_1154 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'percent_1164 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'lt_1174 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'gt_1184 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'pipe_1194 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'amp_1204 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'at_1214 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'dotted_1228 v4 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                    (coe du_ParsesOpExpr'45'shrinks_1378 (coe v12) (coe v1) (coe v10))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                              coe (coe (\ v14 -> v13)))
                             (coe (0 :: Integer)) (coe v12))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesLamParams-shrinks
d_ParsesLamParams'45'shrinks_1386 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLamParams_550 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLamParams'45'shrinks_1386 v0 v1 v2 v3
  = case coe v3 of
      C_plp'45'body_1006 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesExpr'45'shrinks_1272 (coe v9) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_plp'45'arg_1016 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_54 v11 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                           (coe
                              d_ParsesLamParams'45'shrinks_1386 (coe v10) (coe v12) (coe v2)
                              (coe v8))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                     coe (coe (\ v14 -> v13)))
                                    (coe (0 :: Integer)) (coe v10))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesLet-shrinks
d_ParsesLet'45'shrinks_1394 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLet_552 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLet'45'shrinks_1394 v0 v1 v2 v3
  = case coe v3 of
      C_plet'45'single_1030 v6 v8 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                           (coe
                              du_ParsesLetIn'45'shrinks_1406 (coe v6) (coe v1) (coe v2)
                              (coe v11))
                           (coe du_ParsesExpr'45'shrinks_1272 (coe v15) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesLetIn-shrinks
d_ParsesLetIn'45'shrinks_1406 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLetIn_554 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLetIn'45'shrinks_1406 ~v0 ~v1 v2 v3 v4 v5
  = du_ParsesLetIn'45'shrinks_1406 v2 v3 v4 v5
du_ParsesLetIn'45'shrinks_1406 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLetIn_554 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesLetIn'45'shrinks_1406 v0 v1 v2 v3
  = case coe v3 of
      C_plin_1042 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_56 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                           (coe du_ParsesExpr'45'shrinks_1272 (coe v11) (coe v9))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (let v15 = \ v15 -> addInt (coe (1 :: Integer)) (coe v15) in
                                     coe (coe (\ v16 -> v15)))
                                    (coe (0 :: Integer)) (coe v11))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestruct-shrinks
d_ParsesDestruct'45'shrinks_1414 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestruct_556 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestruct'45'shrinks_1414 v0 v1 v2 v3
  = case coe v3 of
      C_pd'45'mk_1054 v5 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
             (coe
                du_ParsesDestructOf'45'shrinks_1424 (coe v5) (coe v1) (coe v2)
                (coe v10))
             (coe du_ParsesExpr'45'shrinks_1272 (coe v0) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestructOf-shrinks
d_ParsesDestructOf'45'shrinks_1424 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructOf_558 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestructOf'45'shrinks_1424 ~v0 v1 v2 v3 v4
  = du_ParsesDestructOf'45'shrinks_1424 v1 v2 v3 v4
du_ParsesDestructOf'45'shrinks_1424 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructOf_558 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesDestructOf'45'shrinks_1424 v0 v1 v2 v3
  = case coe v3 of
      C_pdof_1064 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> coe
                           du_ParsesDestructBranches'45'shrinks_1434 (coe v12) (coe v1)
                           (coe v2) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestructBranches-shrinks
d_ParsesDestructBranches'45'shrinks_1434 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructBranches_560 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestructBranches'45'shrinks_1434 ~v0 v1 v2 v3 v4
  = du_ParsesDestructBranches'45'shrinks_1434 v1 v2 v3 v4
du_ParsesDestructBranches'45'shrinks_1434 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructBranches_560 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesDestructBranches'45'shrinks_1434 v0 v1 v2 v3
  = case coe v3 of
      C_pdb_1080 v7 v8 v11 v12
        -> case coe v0 of
             (:) v13 v14
               -> case coe v14 of
                    (:) v15 v16
                      -> case coe v16 of
                           (:) v17 v18
                             -> coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                  (coe MAlonzo.Code.Data.List.Base.du_length_268 v7)
                                  (coe
                                     du_ParsesRightBranch'45'shrinks_1448 (coe v7) (coe v1) (coe v2)
                                     (coe v12))
                                  (coe du_ParsesExpr'45'shrinks_1272 (coe v18) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesRightBranch-shrinks
d_ParsesRightBranch'45'shrinks_1448 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesRightBranch_562 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesRightBranch'45'shrinks_1448 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_ParsesRightBranch'45'shrinks_1448 v3 v4 v5 v6
du_ParsesRightBranch'45'shrinks_1448 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesRightBranch_562 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesRightBranch'45'shrinks_1448 v0 v1 v2 v3
  = case coe v3 of
      C_prb_1096 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> case coe v15 of
                           (:) v16 v17
                             -> case coe v17 of
                                  (:) v18 v19
                                    -> case coe v1 of
                                         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_60 v20 v21 v22 v23 v24
                                           -> coe
                                                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                (coe
                                                   addInt (coe (1 :: Integer))
                                                   (coe
                                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                                      (coe
                                                         (\ v25 v26 ->
                                                            addInt (coe (1 :: Integer)) (coe v26)))
                                                      (coe (0 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                      (coe
                                                         MAlonzo.Code.Data.List.Base.du_foldr_216
                                                         (coe
                                                            (\ v25 v26 ->
                                                               addInt
                                                                 (coe (1 :: Integer)) (coe v26)))
                                                         (coe (0 :: Integer)) (coe v2))))
                                                (coe
                                                   du_ParsesExpr'45'shrinks_1272 (coe v19)
                                                   (coe v11))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesParenCont-shrinks
d_ParsesParenCont'45'shrinks_1458 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenCont_566 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesParenCont'45'shrinks_1458 ~v0 v1 v2 v3 v4
  = du_ParsesParenCont'45'shrinks_1458 v1 v2 v3 v4
du_ParsesParenCont'45'shrinks_1458 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenCont_566 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesParenCont'45'shrinks_1458 v0 v1 v2 v3
  = case coe v3 of
      C_ppc'45'close_1234
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v2)))
      C_ppc'45'pair_1246 v6 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_58 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                           (coe du_ParsesParenTriple'45'shrinks_1468 (coe v2) (coe v10))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                              (coe du_ParsesExpr'45'shrinks_1272 (coe v12) (coe v9))
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                 (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                       (let v15 = \ v15 -> addInt (coe (1 :: Integer)) (coe v15) in
                                        coe (coe (\ v16 -> v15)))
                                       (coe (0 :: Integer)) (coe v12)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ppc'45'annot_1256 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_68 v11 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                 (coe (\ v13 v14 -> addInt (coe (1 :: Integer)) (coe v14)))
                                 (coe (0 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (coe (\ v13 v14 -> addInt (coe (1 :: Integer)) (coe v14)))
                                    (coe (0 :: Integer)) (coe v2))))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                              (coe
                                 MAlonzo.Code.Once.Parser.TypeRelation.d_ParsesType'45'shrinks_444
                                 (coe v10) (coe v12)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                 (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                       (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                        coe (coe (\ v14 -> v13)))
                                       (coe (0 :: Integer)) (coe v10)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesParenTriple-shrinks
d_ParsesParenTriple'45'shrinks_1468 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenTriple_568 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesParenTriple'45'shrinks_1468 ~v0 ~v1 ~v2 v3 v4
  = du_ParsesParenTriple'45'shrinks_1468 v3 v4
du_ParsesParenTriple'45'shrinks_1468 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenTriple_568 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesParenTriple'45'shrinks_1468 v0 v1
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
