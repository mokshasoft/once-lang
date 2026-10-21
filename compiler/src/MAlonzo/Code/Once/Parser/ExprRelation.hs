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
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type
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
    C_aao'45'TFloat_172 | C_aao'45'word_178
-- Once.Parser.ExprRelation.NotTWord
d_NotTWord_180 a0 = ()
data T_NotTWord_180
  = C_ntw'45'TLParen_182 | C_ntw'45'TRParen_184 |
    C_ntw'45'TLBrace_186 | C_ntw'45'TRBrace_188 | C_ntw'45'TColon_190 |
    C_ntw'45'TEquals_192 | C_ntw'45'TArrow_194 | C_ntw'45'TCaret0_196 |
    C_ntw'45'TCaret1_198 | C_ntw'45'TCaretW_200 |
    C_ntw'45'TLambda_202 | C_ntw'45'TComma_204 |
    C_ntw'45'TSemicolon_206 | C_ntw'45'TAt_208 | C_ntw'45'TPipe_210 |
    C_ntw'45'TDot_212 | C_ntw'45'TPlus_214 | C_ntw'45'TMinus_216 |
    C_ntw'45'TStar_218 | C_ntw'45'TSlash_220 | C_ntw'45'TPercent_222 |
    C_ntw'45'TAmpersand_224 | C_ntw'45'TLt_226 | C_ntw'45'TLe_228 |
    C_ntw'45'TGt_230 | C_ntw'45'TGe_232 | C_ntw'45'TEqEq_234 |
    C_ntw'45'TNeq_236 | C_ntw'45'TBang_238 | C_ntw'45'TNewline_240 |
    C_ntw'45'TEOF_242 | C_ntw'45'TInt_248 | C_ntw'45'TFloat_258 |
    C_ntw'45'TString_262
-- Once.Parser.ExprRelation.NotQualPrefix
d_NotQualPrefix_264 a0 = ()
data T_NotQualPrefix_264
  = C_nqp'45''91''93'_266 | C_nqp'45'TLParen_270 |
    C_nqp'45'TRParen_274 | C_nqp'45'TLBrace_278 |
    C_nqp'45'TRBrace_282 | C_nqp'45'TColon_286 | C_nqp'45'TEquals_290 |
    C_nqp'45'TArrow_294 | C_nqp'45'TCaret0_298 | C_nqp'45'TCaret1_302 |
    C_nqp'45'TCaretW_306 | C_nqp'45'TLambda_310 | C_nqp'45'TComma_314 |
    C_nqp'45'TSemicolon_318 | C_nqp'45'TPipe_322 | C_nqp'45'TDot_326 |
    C_nqp'45'TPlus_330 | C_nqp'45'TMinus_334 | C_nqp'45'TStar_338 |
    C_nqp'45'TSlash_342 | C_nqp'45'TPercent_346 |
    C_nqp'45'TAmpersand_350 | C_nqp'45'TLt_354 | C_nqp'45'TLe_358 |
    C_nqp'45'TGt_362 | C_nqp'45'TGe_366 | C_nqp'45'TEqEq_370 |
    C_nqp'45'TNeq_374 | C_nqp'45'TBang_378 | C_nqp'45'TNewline_382 |
    C_nqp'45'TEOF_386 | C_nqp'45'TWord_392 | C_nqp'45'TInt_400 |
    C_nqp'45'TFloat_412 | C_nqp'45'TString_418 |
    C_nqp'45'TAt'45''91''93'_420 |
    C_nqp'45'TAt'45'cons_426 T_NotTWord_180
-- Once.Parser.ExprRelation.ReservedView
d_ReservedView_430 a0 = ()
data T_ReservedView_430
  = C_rv'45'reserved_434 | C_rv'45'not'45'reserved_436
-- Once.Parser.ExprRelation.reserved-view
d_reserved'45'view_440 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_ReservedView_430
d_reserved'45'view_440 v0
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
         then coe C_rv'45'reserved_434
         else coe C_rv'45'not'45'reserved_436)
-- Once.Parser.ExprRelation.WordEqView
d_WordEqView_458 a0 a1 = ()
data T_WordEqView_458 = C_we'45'match_464 | C_we'45'nomatch_466
-- Once.Parser.ExprRelation.wordEq-view
d_wordEq'45'view_472 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_WordEqView_458
d_wordEq'45'view_472 v0 v1
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
                then coe seq (coe v4) (coe C_we'45'match_464)
                else coe seq (coe v4) (coe C_we'45'nomatch_466)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.ExprRelation.ParsesExpr
d_ParsesExpr_494 a0 a1 a2 = ()
newtype T_ParsesExpr_494 = C_pe'45'mk_544 T_ParsesComp_496
-- Once.Parser.ExprRelation.ParsesComp
d_ParsesComp_496 a0 a1 a2 = ()
data T_ParsesComp_496
  = C_pc'45'mk_556 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesCmp_500
                   T_ParsesCompTail_498
-- Once.Parser.ExprRelation.ParsesCompTail
d_ParsesCompTail_498 a0 a1 a2 a3 = ()
data T_ParsesCompTail_498
  = C_pct'45'done_562 AgdaAny |
    C_pct'45'dot_576 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesCmp_500
                     T_ParsesCompTail_498
-- Once.Parser.ExprRelation.ParsesCmp
d_ParsesCmp_500 a0 a1 a2 = ()
data T_ParsesCmp_500
  = C_pcm'45'noop_584 T_ParsesAdd_502 AgdaAny |
    C_pcm'45'lt_596 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_502 T_ParsesAdd_502 |
    C_pcm'45'le_608 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_502 T_ParsesAdd_502 |
    C_pcm'45'gt_620 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_502 T_ParsesAdd_502 |
    C_pcm'45'ge_632 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_502 T_ParsesAdd_502 |
    C_pcm'45'eq_644 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_502 T_ParsesAdd_502 |
    C_pcm'45'ne_656 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_502 T_ParsesAdd_502
-- Once.Parser.ExprRelation.ParsesAdd
d_ParsesAdd_502 a0 a1 a2 = ()
data T_ParsesAdd_502
  = C_pa'45'mk_668 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesMul_506
                   T_ParsesAddTail_504
-- Once.Parser.ExprRelation.ParsesAddTail
d_ParsesAddTail_504 a0 a1 a2 a3 = ()
data T_ParsesAddTail_504
  = C_pat'45'done_674 AgdaAny |
    C_pat'45'plus_688 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesMul_506
                      T_ParsesAddTail_504 |
    C_pat'45'minus_702 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesMul_506
                       T_ParsesAddTail_504
-- Once.Parser.ExprRelation.ParsesMul
d_ParsesMul_506 a0 a1 a2 = ()
data T_ParsesMul_506
  = C_pm'45'mk_714 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesUnary_510
                   T_ParsesMulTail_508
-- Once.Parser.ExprRelation.ParsesMulTail
d_ParsesMulTail_508 a0 a1 a2 a3 = ()
data T_ParsesMulTail_508
  = C_pmt'45'done_720 AgdaAny |
    C_pmt'45'star_734 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesUnary_510
                      T_ParsesMulTail_508 |
    C_pmt'45'slash_748 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesUnary_510
                       T_ParsesMulTail_508 |
    C_pmt'45'percent_762 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                         MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesUnary_510
                         T_ParsesMulTail_508
-- Once.Parser.ExprRelation.ParsesUnary
d_ParsesUnary_510 a0 a1 a2 = ()
data T_ParsesUnary_510
  = C_pu'45'neg_770 T_ParsesUnary_510 |
    C_pu'45'app_778 T_ParsesApp_512
-- Once.Parser.ExprRelation.ParsesApp
d_ParsesApp_512 a0 a1 a2 = ()
data T_ParsesApp_512
  = C_papp'45'mk_790 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesAtomExpr_516
                     T_ParsesAppTail_514
-- Once.Parser.ExprRelation.ParsesAppTail
d_ParsesAppTail_514 a0 a1 a2 a3 = ()
data T_ParsesAppTail_514
  = C_papp'45'done_796 T_NotAtomStart_18 |
    C_papp'45'arg_810 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_AppArgOk_144
                      T_ParsesAtomExpr_516 T_ParsesAppTail_514
-- Once.Parser.ExprRelation.ParsesAtomExpr
d_ParsesAtomExpr_516 a0 a1 a2 = ()
data T_ParsesAtomExpr_516
  = C_pae'45'unit_814 | C_pae'45'int_822 | C_pae'45'float_834 |
    C_pae'45'var_840 T_NotQualPrefix_264 | C_pae'45'qual_848 |
    C_pae'45'paren_860 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesExpr_494
                       T_ParsesParenCont_534 |
    C_pae'45'lambda_868 T_ParsesLamParams_518 |
    C_pae'45'let_876 T_ParsesLet_520 |
    C_pae'45'destruct_884 T_ParsesDestruct_524 |
    C_pae'45'paren'45'op_892 T_ParsesOpExpr_532
-- Once.Parser.ExprRelation.ParsesLamParams
d_ParsesLamParams_518 a0 a1 a2 = ()
data T_ParsesLamParams_518
  = C_plp'45'body_900 T_ParsesExpr_494 |
    C_plp'45'arg_910 T_ParsesLamParams_518
-- Once.Parser.ExprRelation.ParsesLet
d_ParsesLet_520 a0 a1 a2 = ()
data T_ParsesLet_520
  = C_plet'45'single_924 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                         MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesExpr_494
                         T_ParsesLetIn_522
-- Once.Parser.ExprRelation.ParsesLetIn
d_ParsesLetIn_522 a0 a1 a2 a3 a4 = ()
newtype T_ParsesLetIn_522 = C_plin_936 T_ParsesExpr_494
-- Once.Parser.ExprRelation.ParsesDestruct
d_ParsesDestruct_524 a0 a1 a2 = ()
data T_ParsesDestruct_524
  = C_pd'45'mk_948 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesExpr_494
                   T_ParsesDestructOf_526
-- Once.Parser.ExprRelation.ParsesDestructOf
d_ParsesDestructOf_526 a0 a1 a2 a3 = ()
newtype T_ParsesDestructOf_526
  = C_pdof_958 T_ParsesDestructBranches_528
-- Once.Parser.ExprRelation.ParsesDestructBranches
d_ParsesDestructBranches_528 a0 a1 a2 a3 = ()
data T_ParsesDestructBranches_528
  = C_pdb_974 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
              MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 T_ParsesExpr_494
              T_ParsesRightBranch_530
-- Once.Parser.ExprRelation.ParsesRightBranch
d_ParsesRightBranch_530 a0 a1 a2 a3 a4 a5 = ()
newtype T_ParsesRightBranch_530 = C_prb_990 T_ParsesExpr_494
-- Once.Parser.ExprRelation.ParsesOpExpr
d_ParsesOpExpr_532 a0 a1 a2 a3 = ()
data T_ParsesOpExpr_532
  = C_poe'45'close_998 | C_poe'45'dot_1008 T_ParsesOpExpr_532 |
    C_poe'45'plus_1018 T_ParsesOpExpr_532 |
    C_poe'45'minus_1028 T_ParsesOpExpr_532 |
    C_poe'45'star_1038 T_ParsesOpExpr_532 |
    C_poe'45'slash_1048 T_ParsesOpExpr_532 |
    C_poe'45'percent_1058 T_ParsesOpExpr_532 |
    C_poe'45'lt_1068 T_ParsesOpExpr_532 |
    C_poe'45'gt_1078 T_ParsesOpExpr_532 |
    C_poe'45'pipe_1088 T_ParsesOpExpr_532 |
    C_poe'45'amp_1098 T_ParsesOpExpr_532 |
    C_poe'45'at_1108 T_ParsesOpExpr_532
-- Once.Parser.ExprRelation.ParsesParenCont
d_ParsesParenCont_534 a0 a1 a2 a3 = ()
data T_ParsesParenCont_534
  = C_ppc'45'close_1114 |
    C_ppc'45'pair_1126 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       T_ParsesExpr_494 T_ParsesParenTriple_536 |
    C_ppc'45'annot_1136 MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
-- Once.Parser.ExprRelation.ParsesParenTriple
d_ParsesParenTriple_536 a0 a1 a2 a3 = ()
data T_ParsesParenTriple_536 = C_ppt'45'close_1144
-- Once.Parser.ExprRelation.ParsesExpr-shrinks
d_ParsesExpr'45'shrinks_1152 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesExpr_494 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesExpr'45'shrinks_1152 v0 ~v1 ~v2 v3
  = du_ParsesExpr'45'shrinks_1152 v0 v3
du_ParsesExpr'45'shrinks_1152 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesExpr_494 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesExpr'45'shrinks_1152 v0 v1
  = case coe v1 of
      C_pe'45'mk_544 v5
        -> coe du_ParsesComp'45'shrinks_1160 (coe v0) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesComp-shrinks
d_ParsesComp'45'shrinks_1160 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesComp_496 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesComp'45'shrinks_1160 v0 ~v1 ~v2 v3
  = du_ParsesComp'45'shrinks_1160 v0 v3
du_ParsesComp'45'shrinks_1160 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesComp_496 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesComp'45'shrinks_1160 v0 v1
  = case coe v1 of
      C_pc'45'mk_556 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesCompTail'45'shrinks_1170 (coe v3) (coe v8))
             (coe du_ParsesCmp'45'shrinks_1178 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesCompTail-shrinks
d_ParsesCompTail'45'shrinks_1170 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCompTail_498 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesCompTail'45'shrinks_1170 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesCompTail'45'shrinks_1170 v1 v4
du_ParsesCompTail'45'shrinks_1170 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCompTail_498 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesCompTail'45'shrinks_1170 v0 v1
  = case coe v1 of
      C_pct'45'done_562 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pct'45'dot_576 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesCompTail'45'shrinks_1170 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesCmp'45'shrinks_1178 (coe v11) (coe v8))
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
d_ParsesCmp'45'shrinks_1178 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCmp_500 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesCmp'45'shrinks_1178 v0 ~v1 ~v2 v3
  = du_ParsesCmp'45'shrinks_1178 v0 v3
du_ParsesCmp'45'shrinks_1178 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCmp_500 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesCmp'45'shrinks_1178 v0 v1
  = case coe v1 of
      C_pcm'45'noop_584 v5 v6
        -> coe du_ParsesAdd'45'shrinks_1186 (coe v0) (coe v5)
      C_pcm'45'lt_596 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1186 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1186 (coe v0) (coe v7)))
      C_pcm'45'le_608 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1186 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1186 (coe v0) (coe v7)))
      C_pcm'45'gt_620 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1186 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1186 (coe v0) (coe v7)))
      C_pcm'45'ge_632 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1186 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1186 (coe v0) (coe v7)))
      C_pcm'45'eq_644 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1186 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1186 (coe v0) (coe v7)))
      C_pcm'45'ne_656 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1186 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1186 (coe v0) (coe v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAdd-shrinks
d_ParsesAdd'45'shrinks_1186 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAdd_502 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAdd'45'shrinks_1186 v0 ~v1 ~v2 v3
  = du_ParsesAdd'45'shrinks_1186 v0 v3
du_ParsesAdd'45'shrinks_1186 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAdd_502 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAdd'45'shrinks_1186 v0 v1
  = case coe v1 of
      C_pa'45'mk_668 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesAddTail'45'shrinks_1196 (coe v3) (coe v8))
             (coe du_ParsesMul'45'shrinks_1204 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAddTail-shrinks
d_ParsesAddTail'45'shrinks_1196 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAddTail_504 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAddTail'45'shrinks_1196 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesAddTail'45'shrinks_1196 v1 v4
du_ParsesAddTail'45'shrinks_1196 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAddTail_504 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAddTail'45'shrinks_1196 v0 v1
  = case coe v1 of
      C_pat'45'done_674 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pat'45'plus_688 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1196 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesMul'45'shrinks_1204 (coe v11) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pat'45'minus_702 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1196 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesMul'45'shrinks_1204 (coe v11) (coe v8))
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
d_ParsesMul'45'shrinks_1204 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMul_506 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesMul'45'shrinks_1204 v0 ~v1 ~v2 v3
  = du_ParsesMul'45'shrinks_1204 v0 v3
du_ParsesMul'45'shrinks_1204 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMul_506 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesMul'45'shrinks_1204 v0 v1
  = case coe v1 of
      C_pm'45'mk_714 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesMulTail'45'shrinks_1214 (coe v3) (coe v8))
             (coe du_ParsesUnary'45'shrinks_1222 (coe v0) (coe v5) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesMulTail-shrinks
d_ParsesMulTail'45'shrinks_1214 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMulTail_508 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesMulTail'45'shrinks_1214 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesMulTail'45'shrinks_1214 v1 v4
du_ParsesMulTail'45'shrinks_1214 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMulTail_508 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesMulTail'45'shrinks_1214 v0 v1
  = case coe v1 of
      C_pmt'45'done_720 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pmt'45'star_734 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1214 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1222 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'slash_748 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1214 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1222 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'percent_762 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1214 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1222 (coe v11) (coe v6) (coe v8))
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
d_ParsesUnary'45'shrinks_1222 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesUnary_510 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesUnary'45'shrinks_1222 v0 v1 ~v2 v3
  = du_ParsesUnary'45'shrinks_1222 v0 v1 v3
du_ParsesUnary'45'shrinks_1222 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  T_ParsesUnary_510 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesUnary'45'shrinks_1222 v0 v1 v2
  = case coe v2 of
      C_pu'45'neg_770 v6
        -> case coe v0 of
             (:) v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RUnaryOp_62 v10
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v8)
                           (coe du_ParsesUnary'45'shrinks_1222 (coe v8) (coe v10) (coe v6))
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
      C_pu'45'app_778 v6
        -> coe du_ParsesApp'45'shrinks_1230 (coe v0) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesApp-shrinks
d_ParsesApp'45'shrinks_1230 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesApp_512 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesApp'45'shrinks_1230 v0 ~v1 ~v2 v3
  = du_ParsesApp'45'shrinks_1230 v0 v3
du_ParsesApp'45'shrinks_1230 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesApp_512 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesApp'45'shrinks_1230 v0 v1
  = case coe v1 of
      C_papp'45'mk_790 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesAppTail'45'shrinks_1240 (coe v3) (coe v8))
             (coe
                d_ParsesAtomExpr'45'shrinks_1248 (coe v0) (coe v5) (coe v3)
                (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAppTail-shrinks
d_ParsesAppTail'45'shrinks_1240 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAppTail_514 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAppTail'45'shrinks_1240 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesAppTail'45'shrinks_1240 v1 v4
du_ParsesAppTail'45'shrinks_1240 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAppTail_514 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAppTail'45'shrinks_1240 v0 v1
  = case coe v1 of
      C_papp'45'done_796 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_papp'45'arg_810 v4 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe du_ParsesAppTail'45'shrinks_1240 (coe v4) (coe v10))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                (coe
                   d_ParsesAtomExpr'45'shrinks_1248 (coe v0) (coe v6) (coe v4)
                   (coe v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAtomExpr-shrinks
d_ParsesAtomExpr'45'shrinks_1248 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAtomExpr_516 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAtomExpr'45'shrinks_1248 v0 v1 v2 v3
  = case coe v3 of
      C_pae'45'unit_814
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'int_822
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v7 = \ v7 -> addInt (coe (1 :: Integer)) (coe v7) in
                    coe (coe (\ v8 -> v7)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'float_834
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v9 = \ v9 -> addInt (coe (1 :: Integer)) (coe v9) in
                    coe (coe (\ v10 -> v9)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'var_840 v7
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                    coe (coe (\ v9 -> v8)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'qual_848
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                    coe (coe (\ v9 -> v8)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'paren_860 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
                    (coe
                       du_ParsesParenCont'45'shrinks_1338 (coe v5) (coe v1) (coe v2)
                       (coe v10))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                       (coe du_ParsesExpr'45'shrinks_1152 (coe v12) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                 coe (coe (\ v14 -> v13)))
                                (coe (0 :: Integer)) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'lambda_868 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesLamParams'45'shrinks_1266 (coe v9) (coe v1) (coe v2)
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
      C_pae'45'let_876 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesLet'45'shrinks_1274 (coe v9) (coe v1) (coe v2) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'destruct_884 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesDestruct'45'shrinks_1294 (coe v9) (coe v1) (coe v2)
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
      C_pae'45'paren'45'op_892 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v2) (coe v7))
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
d_ParsesOpExpr'45'shrinks_1258 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesOpExpr_532 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesOpExpr'45'shrinks_1258 ~v0 v1 ~v2 v3 v4
  = du_ParsesOpExpr'45'shrinks_1258 v1 v3 v4
du_ParsesOpExpr'45'shrinks_1258 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesOpExpr_532 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesOpExpr'45'shrinks_1258 v0 v1 v2
  = case coe v2 of
      C_poe'45'close_998
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v1)))
      C_poe'45'dot_1008 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'plus_1018 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'minus_1028 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'star_1038 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'slash_1048 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'percent_1058 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'lt_1068 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'gt_1078 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'pipe_1088 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'amp_1098 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'at_1108 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1258 (coe v9) (coe v1) (coe v7))
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
d_ParsesLamParams'45'shrinks_1266 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLamParams_518 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLamParams'45'shrinks_1266 v0 v1 v2 v3
  = case coe v3 of
      C_plp'45'body_900 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesExpr'45'shrinks_1152 (coe v9) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_plp'45'arg_910 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RLam_44 v11 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                           (coe
                              d_ParsesLamParams'45'shrinks_1266 (coe v10) (coe v12) (coe v2)
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
d_ParsesLet'45'shrinks_1274 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLet_520 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLet'45'shrinks_1274 v0 v1 v2 v3
  = case coe v3 of
      C_plet'45'single_924 v6 v8 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                           (coe
                              du_ParsesLetIn'45'shrinks_1286 (coe v6) (coe v1) (coe v2)
                              (coe v11))
                           (coe du_ParsesExpr'45'shrinks_1152 (coe v15) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesLetIn-shrinks
d_ParsesLetIn'45'shrinks_1286 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLetIn_522 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLetIn'45'shrinks_1286 ~v0 ~v1 v2 v3 v4 v5
  = du_ParsesLetIn'45'shrinks_1286 v2 v3 v4 v5
du_ParsesLetIn'45'shrinks_1286 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLetIn_522 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesLetIn'45'shrinks_1286 v0 v1 v2 v3
  = case coe v3 of
      C_plin_936 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RLet_46 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                           (coe du_ParsesExpr'45'shrinks_1152 (coe v11) (coe v9))
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
d_ParsesDestruct'45'shrinks_1294 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestruct_524 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestruct'45'shrinks_1294 v0 v1 v2 v3
  = case coe v3 of
      C_pd'45'mk_948 v5 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
             (coe
                du_ParsesDestructOf'45'shrinks_1304 (coe v5) (coe v1) (coe v2)
                (coe v10))
             (coe du_ParsesExpr'45'shrinks_1152 (coe v0) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestructOf-shrinks
d_ParsesDestructOf'45'shrinks_1304 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructOf_526 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestructOf'45'shrinks_1304 ~v0 v1 v2 v3 v4
  = du_ParsesDestructOf'45'shrinks_1304 v1 v2 v3 v4
du_ParsesDestructOf'45'shrinks_1304 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructOf_526 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesDestructOf'45'shrinks_1304 v0 v1 v2 v3
  = case coe v3 of
      C_pdof_958 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> coe
                           du_ParsesDestructBranches'45'shrinks_1314 (coe v12) (coe v1)
                           (coe v2) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestructBranches-shrinks
d_ParsesDestructBranches'45'shrinks_1314 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructBranches_528 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestructBranches'45'shrinks_1314 ~v0 v1 v2 v3 v4
  = du_ParsesDestructBranches'45'shrinks_1314 v1 v2 v3 v4
du_ParsesDestructBranches'45'shrinks_1314 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructBranches_528 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesDestructBranches'45'shrinks_1314 v0 v1 v2 v3
  = case coe v3 of
      C_pdb_974 v7 v8 v11 v12
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
                                     du_ParsesRightBranch'45'shrinks_1328 (coe v7) (coe v1) (coe v2)
                                     (coe v12))
                                  (coe du_ParsesExpr'45'shrinks_1152 (coe v18) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesRightBranch-shrinks
d_ParsesRightBranch'45'shrinks_1328 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesRightBranch_530 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesRightBranch'45'shrinks_1328 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_ParsesRightBranch'45'shrinks_1328 v3 v4 v5 v6
du_ParsesRightBranch'45'shrinks_1328 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesRightBranch_530 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesRightBranch'45'shrinks_1328 v0 v1 v2 v3
  = case coe v3 of
      C_prb_990 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> case coe v15 of
                           (:) v16 v17
                             -> case coe v17 of
                                  (:) v18 v19
                                    -> case coe v1 of
                                         MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_50 v20 v21 v22 v23 v24
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
                                                   du_ParsesExpr'45'shrinks_1152 (coe v19)
                                                   (coe v11))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesParenCont-shrinks
d_ParsesParenCont'45'shrinks_1338 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenCont_534 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesParenCont'45'shrinks_1338 ~v0 v1 v2 v3 v4
  = du_ParsesParenCont'45'shrinks_1338 v1 v2 v3 v4
du_ParsesParenCont'45'shrinks_1338 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenCont_534 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesParenCont'45'shrinks_1338 v0 v1 v2 v3
  = case coe v3 of
      C_ppc'45'close_1114
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v2)))
      C_ppc'45'pair_1126 v6 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RPair_48 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                           (coe du_ParsesParenTriple'45'shrinks_1348 (coe v2) (coe v10))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                              (coe du_ParsesExpr'45'shrinks_1152 (coe v12) (coe v9))
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
      C_ppc'45'annot_1136 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Syntax.C_RAnnot_58 v11 v12
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
d_ParsesParenTriple'45'shrinks_1348 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenTriple_536 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesParenTriple'45'shrinks_1348 ~v0 ~v1 ~v2 v3 v4
  = du_ParsesParenTriple'45'shrinks_1348 v3 v4
du_ParsesParenTriple'45'shrinks_1348 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenTriple_536 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesParenTriple'45'shrinks_1348 v0 v1
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
