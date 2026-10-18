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
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.TypeRelation
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
-- Once.Parser.ExprRelation.NotAtomStart
d_NotAtomStart_18 a0 = ()
data T_NotAtomStart_18
  = C_nas'45''91''93'_20 | C_nas'45'word'45'res_26 |
    C_nas'45'TRParen_30 | C_nas'45'TLBrace_34 | C_nas'45'TRBrace_38 |
    C_nas'45'TColon_42 | C_nas'45'TEquals_46 | C_nas'45'TArrow_50 |
    C_nas'45'TCaret0_54 | C_nas'45'TCaret1_58 | C_nas'45'TCaretW_62 |
    C_nas'45'TComma_66 | C_nas'45'TSemicolon_70 | C_nas'45'TAt_74 |
    C_nas'45'TPipe_78 | C_nas'45'TDot_82 | C_nas'45'TPlus_86 |
    C_nas'45'TMinus_90 | C_nas'45'TStar_94 | C_nas'45'TSlash_98 |
    C_nas'45'TPercent_102 | C_nas'45'TAmpersand_106 |
    C_nas'45'TLt_110 | C_nas'45'TLe_114 | C_nas'45'TGt_118 |
    C_nas'45'TGe_122 | C_nas'45'TEqEq_126 | C_nas'45'TNeq_130 |
    C_nas'45'TBang_134 | C_nas'45'TNewline_138 | C_nas'45'TEOF_142
-- Once.Parser.ExprRelation.AppArgOk
d_AppArgOk_144 a0 = ()
data T_AppArgOk_144
  = C_aao'45'TLParen_148 | C_aao'45'TLambda_152 | C_aao'45'TInt_160 |
    C_aao'45'TFloat_172 | C_aao'45'TString_178 | C_aao'45'word_184
-- Once.Parser.ExprRelation.NotTWord
d_NotTWord_186 a0 = ()
data T_NotTWord_186
  = C_ntw'45'TLParen_188 | C_ntw'45'TRParen_190 |
    C_ntw'45'TLBrace_192 | C_ntw'45'TRBrace_194 | C_ntw'45'TColon_196 |
    C_ntw'45'TEquals_198 | C_ntw'45'TArrow_200 | C_ntw'45'TCaret0_202 |
    C_ntw'45'TCaret1_204 | C_ntw'45'TCaretW_206 |
    C_ntw'45'TLambda_208 | C_ntw'45'TComma_210 |
    C_ntw'45'TSemicolon_212 | C_ntw'45'TAt_214 | C_ntw'45'TPipe_216 |
    C_ntw'45'TDot_218 | C_ntw'45'TPlus_220 | C_ntw'45'TMinus_222 |
    C_ntw'45'TStar_224 | C_ntw'45'TSlash_226 | C_ntw'45'TPercent_228 |
    C_ntw'45'TAmpersand_230 | C_ntw'45'TLt_232 | C_ntw'45'TLe_234 |
    C_ntw'45'TGt_236 | C_ntw'45'TGe_238 | C_ntw'45'TEqEq_240 |
    C_ntw'45'TNeq_242 | C_ntw'45'TBang_244 | C_ntw'45'TNewline_246 |
    C_ntw'45'TEOF_248 | C_ntw'45'TInt_254 | C_ntw'45'TFloat_264 |
    C_ntw'45'TString_268
-- Once.Parser.ExprRelation.NotQualPrefix
d_NotQualPrefix_270 a0 = ()
data T_NotQualPrefix_270
  = C_nqp'45''91''93'_272 | C_nqp'45'TLParen_276 |
    C_nqp'45'TRParen_280 | C_nqp'45'TLBrace_284 |
    C_nqp'45'TRBrace_288 | C_nqp'45'TColon_292 | C_nqp'45'TEquals_296 |
    C_nqp'45'TArrow_300 | C_nqp'45'TCaret0_304 | C_nqp'45'TCaret1_308 |
    C_nqp'45'TCaretW_312 | C_nqp'45'TLambda_316 | C_nqp'45'TComma_320 |
    C_nqp'45'TSemicolon_324 | C_nqp'45'TPipe_328 | C_nqp'45'TDot_332 |
    C_nqp'45'TPlus_336 | C_nqp'45'TMinus_340 | C_nqp'45'TStar_344 |
    C_nqp'45'TSlash_348 | C_nqp'45'TPercent_352 |
    C_nqp'45'TAmpersand_356 | C_nqp'45'TLt_360 | C_nqp'45'TLe_364 |
    C_nqp'45'TGt_368 | C_nqp'45'TGe_372 | C_nqp'45'TEqEq_376 |
    C_nqp'45'TNeq_380 | C_nqp'45'TBang_384 | C_nqp'45'TNewline_388 |
    C_nqp'45'TEOF_392 | C_nqp'45'TWord_398 | C_nqp'45'TInt_406 |
    C_nqp'45'TFloat_418 | C_nqp'45'TString_424 |
    C_nqp'45'TAt'45''91''93'_426 |
    C_nqp'45'TAt'45'cons_432 T_NotTWord_186
-- Once.Parser.ExprRelation.ReservedView
d_ReservedView_436 a0 = ()
data T_ReservedView_436
  = C_rv'45'reserved_440 | C_rv'45'not'45'reserved_442
-- Once.Parser.ExprRelation.reserved-view
d_reserved'45'view_446 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_ReservedView_436
d_reserved'45'view_446 v0
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
         then coe C_rv'45'reserved_440
         else coe C_rv'45'not'45'reserved_442)
-- Once.Parser.ExprRelation.WordEqView
d_WordEqView_464 a0 a1 = ()
data T_WordEqView_464 = C_we'45'match_470 | C_we'45'nomatch_472
-- Once.Parser.ExprRelation.wordEq-view
d_wordEq'45'view_478 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_WordEqView_464
d_wordEq'45'view_478 v0 v1
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
                then coe seq (coe v4) (coe C_we'45'match_470)
                else coe seq (coe v4) (coe C_we'45'nomatch_472)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.ExprRelation.ParsesExpr
d_ParsesExpr_500 a0 a1 a2 = ()
newtype T_ParsesExpr_500 = C_pe'45'mk_550 T_ParsesComp_502
-- Once.Parser.ExprRelation.ParsesComp
d_ParsesComp_502 a0 a1 a2 = ()
data T_ParsesComp_502
  = C_pc'45'mk_562 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesCmp_506
                   T_ParsesCompTail_504
-- Once.Parser.ExprRelation.ParsesCompTail
d_ParsesCompTail_504 a0 a1 a2 a3 = ()
data T_ParsesCompTail_504
  = C_pct'45'done_568 AgdaAny |
    C_pct'45'dot_582 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesCmp_506
                     T_ParsesCompTail_504
-- Once.Parser.ExprRelation.ParsesCmp
d_ParsesCmp_506 a0 a1 a2 = ()
data T_ParsesCmp_506
  = C_pcm'45'noop_590 T_ParsesAdd_508 AgdaAny |
    C_pcm'45'lt_602 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_508 T_ParsesAdd_508 |
    C_pcm'45'le_614 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_508 T_ParsesAdd_508 |
    C_pcm'45'gt_626 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_508 T_ParsesAdd_508 |
    C_pcm'45'ge_638 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_508 T_ParsesAdd_508 |
    C_pcm'45'eq_650 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_508 T_ParsesAdd_508 |
    C_pcm'45'ne_662 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_508 T_ParsesAdd_508
-- Once.Parser.ExprRelation.ParsesAdd
d_ParsesAdd_508 a0 a1 a2 = ()
data T_ParsesAdd_508
  = C_pa'45'mk_674 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesMul_512
                   T_ParsesAddTail_510
-- Once.Parser.ExprRelation.ParsesAddTail
d_ParsesAddTail_510 a0 a1 a2 a3 = ()
data T_ParsesAddTail_510
  = C_pat'45'done_680 AgdaAny |
    C_pat'45'plus_694 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesMul_512
                      T_ParsesAddTail_510 |
    C_pat'45'minus_708 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesMul_512
                       T_ParsesAddTail_510
-- Once.Parser.ExprRelation.ParsesMul
d_ParsesMul_512 a0 a1 a2 = ()
data T_ParsesMul_512
  = C_pm'45'mk_720 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesUnary_516
                   T_ParsesMulTail_514
-- Once.Parser.ExprRelation.ParsesMulTail
d_ParsesMulTail_514 a0 a1 a2 a3 = ()
data T_ParsesMulTail_514
  = C_pmt'45'done_726 AgdaAny |
    C_pmt'45'star_740 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesUnary_516
                      T_ParsesMulTail_514 |
    C_pmt'45'slash_754 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesUnary_516
                       T_ParsesMulTail_514 |
    C_pmt'45'percent_768 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                         MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesUnary_516
                         T_ParsesMulTail_514
-- Once.Parser.ExprRelation.ParsesUnary
d_ParsesUnary_516 a0 a1 a2 = ()
data T_ParsesUnary_516
  = C_pu'45'neg_776 T_ParsesUnary_516 |
    C_pu'45'app_784 T_ParsesApp_518
-- Once.Parser.ExprRelation.ParsesApp
d_ParsesApp_518 a0 a1 a2 = ()
data T_ParsesApp_518
  = C_papp'45'mk_796 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesAtomExpr_522
                     T_ParsesAppTail_520
-- Once.Parser.ExprRelation.ParsesAppTail
d_ParsesAppTail_520 a0 a1 a2 a3 = ()
data T_ParsesAppTail_520
  = C_papp'45'done_802 T_NotAtomStart_18 |
    C_papp'45'arg_816 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_AppArgOk_144
                      T_ParsesAtomExpr_522 T_ParsesAppTail_520
-- Once.Parser.ExprRelation.ParsesAtomExpr
d_ParsesAtomExpr_522 a0 a1 a2 = ()
data T_ParsesAtomExpr_522
  = C_pae'45'unit_820 | C_pae'45'int_828 | C_pae'45'float_840 |
    C_pae'45'str_846 | C_pae'45'var_852 T_NotQualPrefix_270 |
    C_pae'45'qual_860 |
    C_pae'45'paren_872 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesExpr_500
                       T_ParsesParenCont_540 |
    C_pae'45'lambda_880 T_ParsesLamParams_524 |
    C_pae'45'let_888 T_ParsesLet_526 |
    C_pae'45'destruct_896 T_ParsesDestruct_530 |
    C_pae'45'paren'45'op_904 T_ParsesOpExpr_538
-- Once.Parser.ExprRelation.ParsesLamParams
d_ParsesLamParams_524 a0 a1 a2 = ()
data T_ParsesLamParams_524
  = C_plp'45'body_912 T_ParsesExpr_500 |
    C_plp'45'arg_922 T_ParsesLamParams_524
-- Once.Parser.ExprRelation.ParsesLet
d_ParsesLet_526 a0 a1 a2 = ()
data T_ParsesLet_526
  = C_plet'45'single_936 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                         MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesExpr_500
                         T_ParsesLetIn_528
-- Once.Parser.ExprRelation.ParsesLetIn
d_ParsesLetIn_528 a0 a1 a2 a3 a4 = ()
newtype T_ParsesLetIn_528 = C_plin_948 T_ParsesExpr_500
-- Once.Parser.ExprRelation.ParsesDestruct
d_ParsesDestruct_530 a0 a1 a2 = ()
data T_ParsesDestruct_530
  = C_pd'45'mk_960 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesExpr_500
                   T_ParsesDestructOf_532
-- Once.Parser.ExprRelation.ParsesDestructOf
d_ParsesDestructOf_532 a0 a1 a2 a3 = ()
newtype T_ParsesDestructOf_532
  = C_pdof_970 T_ParsesDestructBranches_534
-- Once.Parser.ExprRelation.ParsesDestructBranches
d_ParsesDestructBranches_534 a0 a1 a2 a3 = ()
data T_ParsesDestructBranches_534
  = C_pdb_986 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
              MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 T_ParsesExpr_500
              T_ParsesRightBranch_536
-- Once.Parser.ExprRelation.ParsesRightBranch
d_ParsesRightBranch_536 a0 a1 a2 a3 a4 a5 = ()
newtype T_ParsesRightBranch_536 = C_prb_1002 T_ParsesExpr_500
-- Once.Parser.ExprRelation.ParsesOpExpr
d_ParsesOpExpr_538 a0 a1 a2 a3 = ()
data T_ParsesOpExpr_538
  = C_poe'45'close_1010 | C_poe'45'dot_1020 T_ParsesOpExpr_538 |
    C_poe'45'plus_1030 T_ParsesOpExpr_538 |
    C_poe'45'minus_1040 T_ParsesOpExpr_538 |
    C_poe'45'star_1050 T_ParsesOpExpr_538 |
    C_poe'45'slash_1060 T_ParsesOpExpr_538 |
    C_poe'45'percent_1070 T_ParsesOpExpr_538 |
    C_poe'45'lt_1080 T_ParsesOpExpr_538 |
    C_poe'45'gt_1090 T_ParsesOpExpr_538 |
    C_poe'45'pipe_1100 T_ParsesOpExpr_538 |
    C_poe'45'amp_1110 T_ParsesOpExpr_538 |
    C_poe'45'at_1120 T_ParsesOpExpr_538
-- Once.Parser.ExprRelation.ParsesParenCont
d_ParsesParenCont_540 a0 a1 a2 a3 = ()
data T_ParsesParenCont_540
  = C_ppc'45'close_1126 |
    C_ppc'45'pair_1138 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       T_ParsesExpr_500 T_ParsesParenTriple_542 |
    C_ppc'45'annot_1148 MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
-- Once.Parser.ExprRelation.ParsesParenTriple
d_ParsesParenTriple_542 a0 a1 a2 a3 = ()
data T_ParsesParenTriple_542 = C_ppt'45'close_1156
-- Once.Parser.ExprRelation.ParsesExpr-shrinks
d_ParsesExpr'45'shrinks_1164 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesExpr_500 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesExpr'45'shrinks_1164 v0 ~v1 ~v2 v3
  = du_ParsesExpr'45'shrinks_1164 v0 v3
du_ParsesExpr'45'shrinks_1164 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesExpr_500 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesExpr'45'shrinks_1164 v0 v1
  = case coe v1 of
      C_pe'45'mk_550 v5
        -> coe du_ParsesComp'45'shrinks_1172 (coe v0) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesComp-shrinks
d_ParsesComp'45'shrinks_1172 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesComp_502 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesComp'45'shrinks_1172 v0 ~v1 ~v2 v3
  = du_ParsesComp'45'shrinks_1172 v0 v3
du_ParsesComp'45'shrinks_1172 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesComp_502 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesComp'45'shrinks_1172 v0 v1
  = case coe v1 of
      C_pc'45'mk_562 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesCompTail'45'shrinks_1182 (coe v3) (coe v8))
             (coe du_ParsesCmp'45'shrinks_1190 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesCompTail-shrinks
d_ParsesCompTail'45'shrinks_1182 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCompTail_504 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesCompTail'45'shrinks_1182 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesCompTail'45'shrinks_1182 v1 v4
du_ParsesCompTail'45'shrinks_1182 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCompTail_504 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesCompTail'45'shrinks_1182 v0 v1
  = case coe v1 of
      C_pct'45'done_568 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pct'45'dot_582 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesCompTail'45'shrinks_1182 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesCmp'45'shrinks_1190 (coe v11) (coe v8))
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
d_ParsesCmp'45'shrinks_1190 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCmp_506 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesCmp'45'shrinks_1190 v0 ~v1 ~v2 v3
  = du_ParsesCmp'45'shrinks_1190 v0 v3
du_ParsesCmp'45'shrinks_1190 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCmp_506 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesCmp'45'shrinks_1190 v0 v1
  = case coe v1 of
      C_pcm'45'noop_590 v5 v6
        -> coe du_ParsesAdd'45'shrinks_1198 (coe v0) (coe v5)
      C_pcm'45'lt_602 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1198 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1198 (coe v0) (coe v7)))
      C_pcm'45'le_614 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1198 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1198 (coe v0) (coe v7)))
      C_pcm'45'gt_626 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1198 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1198 (coe v0) (coe v7)))
      C_pcm'45'ge_638 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1198 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1198 (coe v0) (coe v7)))
      C_pcm'45'eq_650 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1198 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1198 (coe v0) (coe v7)))
      C_pcm'45'ne_662 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1198 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1198 (coe v0) (coe v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAdd-shrinks
d_ParsesAdd'45'shrinks_1198 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAdd_508 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAdd'45'shrinks_1198 v0 ~v1 ~v2 v3
  = du_ParsesAdd'45'shrinks_1198 v0 v3
du_ParsesAdd'45'shrinks_1198 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAdd_508 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAdd'45'shrinks_1198 v0 v1
  = case coe v1 of
      C_pa'45'mk_674 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesAddTail'45'shrinks_1208 (coe v3) (coe v8))
             (coe du_ParsesMul'45'shrinks_1216 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAddTail-shrinks
d_ParsesAddTail'45'shrinks_1208 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAddTail_510 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAddTail'45'shrinks_1208 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesAddTail'45'shrinks_1208 v1 v4
du_ParsesAddTail'45'shrinks_1208 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAddTail_510 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAddTail'45'shrinks_1208 v0 v1
  = case coe v1 of
      C_pat'45'done_680 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pat'45'plus_694 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1208 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesMul'45'shrinks_1216 (coe v11) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pat'45'minus_708 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1208 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesMul'45'shrinks_1216 (coe v11) (coe v8))
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
-- Once.Parser.ExprRelation.ParsesMul-shrinks
d_ParsesMul'45'shrinks_1216 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMul_512 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesMul'45'shrinks_1216 v0 ~v1 ~v2 v3
  = du_ParsesMul'45'shrinks_1216 v0 v3
du_ParsesMul'45'shrinks_1216 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMul_512 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesMul'45'shrinks_1216 v0 v1
  = case coe v1 of
      C_pm'45'mk_720 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesMulTail'45'shrinks_1226 (coe v3) (coe v8))
             (coe du_ParsesUnary'45'shrinks_1234 (coe v0) (coe v5) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesMulTail-shrinks
d_ParsesMulTail'45'shrinks_1226 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMulTail_514 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesMulTail'45'shrinks_1226 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesMulTail'45'shrinks_1226 v1 v4
du_ParsesMulTail'45'shrinks_1226 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMulTail_514 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesMulTail'45'shrinks_1226 v0 v1
  = case coe v1 of
      C_pmt'45'done_726 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pmt'45'star_740 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1226 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1234 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'slash_754 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1226 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1234 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'percent_768 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1226 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1234 (coe v11) (coe v6) (coe v8))
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
-- Once.Parser.ExprRelation.ParsesUnary-shrinks
d_ParsesUnary'45'shrinks_1234 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesUnary_516 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesUnary'45'shrinks_1234 v0 v1 ~v2 v3
  = du_ParsesUnary'45'shrinks_1234 v0 v1 v3
du_ParsesUnary'45'shrinks_1234 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  T_ParsesUnary_516 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesUnary'45'shrinks_1234 v0 v1 v2
  = case coe v2 of
      C_pu'45'neg_776 v6
        -> case coe v0 of
             (:) v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64 v10
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v8)
                           (coe du_ParsesUnary'45'shrinks_1234 (coe v8) (coe v10) (coe v6))
                           (coe
                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (let v11 = \ v11 -> addInt (coe (1 :: Integer)) (coe v11) in
                                     coe (coe (\ v12 -> v11)))
                                    (coe (0 :: Integer)) (coe v8))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pu'45'app_784 v6
        -> coe du_ParsesApp'45'shrinks_1242 (coe v0) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesApp-shrinks
d_ParsesApp'45'shrinks_1242 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesApp_518 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesApp'45'shrinks_1242 v0 ~v1 ~v2 v3
  = du_ParsesApp'45'shrinks_1242 v0 v3
du_ParsesApp'45'shrinks_1242 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesApp_518 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesApp'45'shrinks_1242 v0 v1
  = case coe v1 of
      C_papp'45'mk_796 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesAppTail'45'shrinks_1252 (coe v3) (coe v8))
             (coe
                d_ParsesAtomExpr'45'shrinks_1260 (coe v0) (coe v5) (coe v3)
                (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAppTail-shrinks
d_ParsesAppTail'45'shrinks_1252 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAppTail_520 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAppTail'45'shrinks_1252 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesAppTail'45'shrinks_1252 v1 v4
du_ParsesAppTail'45'shrinks_1252 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAppTail_520 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAppTail'45'shrinks_1252 v0 v1
  = case coe v1 of
      C_papp'45'done_802 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_papp'45'arg_816 v4 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe du_ParsesAppTail'45'shrinks_1252 (coe v4) (coe v10))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                (coe
                   d_ParsesAtomExpr'45'shrinks_1260 (coe v0) (coe v6) (coe v4)
                   (coe v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAtomExpr-shrinks
d_ParsesAtomExpr'45'shrinks_1260 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAtomExpr_522 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAtomExpr'45'shrinks_1260 v0 v1 v2 v3
  = case coe v3 of
      C_pae'45'unit_820
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'int_828
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v7 = \ v7 -> addInt (coe (1 :: Integer)) (coe v7) in
                    coe (coe (\ v8 -> v7)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'float_840
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v9 = \ v9 -> addInt (coe (1 :: Integer)) (coe v9) in
                    coe (coe (\ v10 -> v9)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'str_846
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'var_852 v7
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                    coe (coe (\ v9 -> v8)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'qual_860
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                    coe (coe (\ v9 -> v8)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'paren_872 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
                    (coe
                       du_ParsesParenCont'45'shrinks_1350 (coe v5) (coe v1) (coe v2)
                       (coe v10))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                       (coe du_ParsesExpr'45'shrinks_1164 (coe v12) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                 coe (coe (\ v14 -> v13)))
                                (coe (0 :: Integer)) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'lambda_880 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesLamParams'45'shrinks_1278 (coe v9) (coe v1) (coe v2)
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
      C_pae'45'let_888 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesLet'45'shrinks_1286 (coe v9) (coe v1) (coe v2) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'destruct_896 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesDestruct'45'shrinks_1306 (coe v9) (coe v1) (coe v2)
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
      C_pae'45'paren'45'op_904 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v2) (coe v7))
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
d_ParsesOpExpr'45'shrinks_1270 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesOpExpr_538 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesOpExpr'45'shrinks_1270 ~v0 v1 ~v2 v3 v4
  = du_ParsesOpExpr'45'shrinks_1270 v1 v3 v4
du_ParsesOpExpr'45'shrinks_1270 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesOpExpr_538 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesOpExpr'45'shrinks_1270 v0 v1 v2
  = case coe v2 of
      C_poe'45'close_1010
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v1)))
      C_poe'45'dot_1020 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'plus_1030 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'minus_1040 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'star_1050 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'slash_1060 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'percent_1070 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'lt_1080 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'gt_1090 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'pipe_1100 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'amp_1110 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'at_1120 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1270 (coe v9) (coe v1) (coe v7))
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
-- Once.Parser.ExprRelation.ParsesLamParams-shrinks
d_ParsesLamParams'45'shrinks_1278 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLamParams_524 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLamParams'45'shrinks_1278 v0 v1 v2 v3
  = case coe v3 of
      C_plp'45'body_912 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesExpr'45'shrinks_1164 (coe v9) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_plp'45'arg_922 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v11 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                           (coe
                              d_ParsesLamParams'45'shrinks_1278 (coe v10) (coe v12) (coe v2)
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
d_ParsesLet'45'shrinks_1286 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLet_526 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLet'45'shrinks_1286 v0 v1 v2 v3
  = case coe v3 of
      C_plet'45'single_936 v6 v8 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                           (coe
                              du_ParsesLetIn'45'shrinks_1298 (coe v6) (coe v1) (coe v2)
                              (coe v11))
                           (coe du_ParsesExpr'45'shrinks_1164 (coe v15) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesLetIn-shrinks
d_ParsesLetIn'45'shrinks_1298 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLetIn_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLetIn'45'shrinks_1298 ~v0 ~v1 v2 v3 v4 v5
  = du_ParsesLetIn'45'shrinks_1298 v2 v3 v4 v5
du_ParsesLetIn'45'shrinks_1298 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLetIn_528 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesLetIn'45'shrinks_1298 v0 v1 v2 v3
  = case coe v3 of
      C_plin_948 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                           (coe du_ParsesExpr'45'shrinks_1164 (coe v11) (coe v9))
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
d_ParsesDestruct'45'shrinks_1306 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestruct_530 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestruct'45'shrinks_1306 v0 v1 v2 v3
  = case coe v3 of
      C_pd'45'mk_960 v5 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
             (coe
                du_ParsesDestructOf'45'shrinks_1316 (coe v5) (coe v1) (coe v2)
                (coe v10))
             (coe du_ParsesExpr'45'shrinks_1164 (coe v0) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestructOf-shrinks
d_ParsesDestructOf'45'shrinks_1316 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructOf_532 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestructOf'45'shrinks_1316 ~v0 v1 v2 v3 v4
  = du_ParsesDestructOf'45'shrinks_1316 v1 v2 v3 v4
du_ParsesDestructOf'45'shrinks_1316 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructOf_532 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesDestructOf'45'shrinks_1316 v0 v1 v2 v3
  = case coe v3 of
      C_pdof_970 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> coe
                           du_ParsesDestructBranches'45'shrinks_1326 (coe v12) (coe v1)
                           (coe v2) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestructBranches-shrinks
d_ParsesDestructBranches'45'shrinks_1326 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructBranches_534 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestructBranches'45'shrinks_1326 ~v0 v1 v2 v3 v4
  = du_ParsesDestructBranches'45'shrinks_1326 v1 v2 v3 v4
du_ParsesDestructBranches'45'shrinks_1326 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructBranches_534 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesDestructBranches'45'shrinks_1326 v0 v1 v2 v3
  = case coe v3 of
      C_pdb_986 v7 v8 v11 v12
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
                                     du_ParsesRightBranch'45'shrinks_1340 (coe v7) (coe v1) (coe v2)
                                     (coe v12))
                                  (coe du_ParsesExpr'45'shrinks_1164 (coe v18) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesRightBranch-shrinks
d_ParsesRightBranch'45'shrinks_1340 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesRightBranch_536 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesRightBranch'45'shrinks_1340 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_ParsesRightBranch'45'shrinks_1340 v3 v4 v5 v6
du_ParsesRightBranch'45'shrinks_1340 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesRightBranch_536 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesRightBranch'45'shrinks_1340 v0 v1 v2 v3
  = case coe v3 of
      C_prb_1002 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> case coe v15 of
                           (:) v16 v17
                             -> case coe v17 of
                                  (:) v18 v19
                                    -> case coe v1 of
                                         MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v20 v21 v22 v23 v24
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
                                                   du_ParsesExpr'45'shrinks_1164 (coe v19)
                                                   (coe v11))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesParenCont-shrinks
d_ParsesParenCont'45'shrinks_1350 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenCont_540 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesParenCont'45'shrinks_1350 ~v0 v1 v2 v3 v4
  = du_ParsesParenCont'45'shrinks_1350 v1 v2 v3 v4
du_ParsesParenCont'45'shrinks_1350 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenCont_540 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesParenCont'45'shrinks_1350 v0 v1 v2 v3
  = case coe v3 of
      C_ppc'45'close_1126
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v2)))
      C_ppc'45'pair_1138 v6 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                           (coe du_ParsesParenTriple'45'shrinks_1360 (coe v2) (coe v10))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                              (coe du_ParsesExpr'45'shrinks_1164 (coe v12) (coe v9))
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
      C_ppc'45'annot_1148 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_60 v11 v12
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
d_ParsesParenTriple'45'shrinks_1360 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenTriple_542 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesParenTriple'45'shrinks_1360 ~v0 ~v1 ~v2 v3 v4
  = du_ParsesParenTriple'45'shrinks_1360 v3 v4
du_ParsesParenTriple'45'shrinks_1360 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenTriple_542 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesParenTriple'45'shrinks_1360 v0 v1
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
