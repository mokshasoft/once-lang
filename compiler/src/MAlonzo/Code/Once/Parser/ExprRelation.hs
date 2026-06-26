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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.ExprRelation.isReserved
d_isReserved_6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isReserved_6 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         l | (==) l ("Left" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("Right" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("destruct" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("in" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("let" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("of" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Parser.ExprRelation.NotDot
d_NotDot_8 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotDot_8 = erased
-- Once.Parser.ExprRelation.NotAdd
d_NotAdd_10 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotAdd_10 = erased
-- Once.Parser.ExprRelation.NotMul
d_NotMul_12 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotMul_12 = erased
-- Once.Parser.ExprRelation.NotCmp
d_NotCmp_14 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_NotCmp_14 = erased
-- Once.Parser.ExprRelation.NotAtomStart
d_NotAtomStart_16 a0 = ()
data T_NotAtomStart_16
  = C_nas'45''91''93'_18 | C_nas'45'word'45'res_24 |
    C_nas'45'TRParen_28 | C_nas'45'TLBrace_32 | C_nas'45'TRBrace_36 |
    C_nas'45'TColon_40 | C_nas'45'TEquals_44 | C_nas'45'TArrow_48 |
    C_nas'45'TCaret0_52 | C_nas'45'TCaret1_56 | C_nas'45'TCaretW_60 |
    C_nas'45'TComma_64 | C_nas'45'TSemicolon_68 | C_nas'45'TAt_72 |
    C_nas'45'TPipe_76 | C_nas'45'TDot_80 | C_nas'45'TPlus_84 |
    C_nas'45'TMinus_88 | C_nas'45'TStar_92 | C_nas'45'TSlash_96 |
    C_nas'45'TPercent_100 | C_nas'45'TAmpersand_104 |
    C_nas'45'TLt_108 | C_nas'45'TLe_112 | C_nas'45'TGt_116 |
    C_nas'45'TGe_120 | C_nas'45'TEqEq_124 | C_nas'45'TNeq_128 |
    C_nas'45'TBang_132 | C_nas'45'TNewline_136 | C_nas'45'TEOF_140
-- Once.Parser.ExprRelation.AppArgOk
d_AppArgOk_142 a0 = ()
data T_AppArgOk_142
  = C_aao'45'TLParen_146 | C_aao'45'TLambda_150 | C_aao'45'TInt_156 |
    C_aao'45'TString_162 | C_aao'45'word_168
-- Once.Parser.ExprRelation.NotTWord
d_NotTWord_170 a0 = ()
data T_NotTWord_170
  = C_ntw'45'TLParen_172 | C_ntw'45'TRParen_174 |
    C_ntw'45'TLBrace_176 | C_ntw'45'TRBrace_178 | C_ntw'45'TColon_180 |
    C_ntw'45'TEquals_182 | C_ntw'45'TArrow_184 | C_ntw'45'TCaret0_186 |
    C_ntw'45'TCaret1_188 | C_ntw'45'TCaretW_190 |
    C_ntw'45'TLambda_192 | C_ntw'45'TComma_194 |
    C_ntw'45'TSemicolon_196 | C_ntw'45'TAt_198 | C_ntw'45'TPipe_200 |
    C_ntw'45'TDot_202 | C_ntw'45'TPlus_204 | C_ntw'45'TMinus_206 |
    C_ntw'45'TStar_208 | C_ntw'45'TSlash_210 | C_ntw'45'TPercent_212 |
    C_ntw'45'TAmpersand_214 | C_ntw'45'TLt_216 | C_ntw'45'TLe_218 |
    C_ntw'45'TGt_220 | C_ntw'45'TGe_222 | C_ntw'45'TEqEq_224 |
    C_ntw'45'TNeq_226 | C_ntw'45'TBang_228 | C_ntw'45'TNewline_230 |
    C_ntw'45'TEOF_232 | C_ntw'45'TInt_236 | C_ntw'45'TString_240
-- Once.Parser.ExprRelation.NotQualPrefix
d_NotQualPrefix_242 a0 = ()
data T_NotQualPrefix_242
  = C_nqp'45''91''93'_244 | C_nqp'45'TLParen_248 |
    C_nqp'45'TRParen_252 | C_nqp'45'TLBrace_256 |
    C_nqp'45'TRBrace_260 | C_nqp'45'TColon_264 | C_nqp'45'TEquals_268 |
    C_nqp'45'TArrow_272 | C_nqp'45'TCaret0_276 | C_nqp'45'TCaret1_280 |
    C_nqp'45'TCaretW_284 | C_nqp'45'TLambda_288 | C_nqp'45'TComma_292 |
    C_nqp'45'TSemicolon_296 | C_nqp'45'TPipe_300 | C_nqp'45'TDot_304 |
    C_nqp'45'TPlus_308 | C_nqp'45'TMinus_312 | C_nqp'45'TStar_316 |
    C_nqp'45'TSlash_320 | C_nqp'45'TPercent_324 |
    C_nqp'45'TAmpersand_328 | C_nqp'45'TLt_332 | C_nqp'45'TLe_336 |
    C_nqp'45'TGt_340 | C_nqp'45'TGe_344 | C_nqp'45'TEqEq_348 |
    C_nqp'45'TNeq_352 | C_nqp'45'TBang_356 | C_nqp'45'TNewline_360 |
    C_nqp'45'TEOF_364 | C_nqp'45'TWord_370 | C_nqp'45'TInt_376 |
    C_nqp'45'TString_382 | C_nqp'45'TAt'45''91''93'_384 |
    C_nqp'45'TAt'45'cons_390 T_NotTWord_170
-- Once.Parser.ExprRelation.ReservedView
d_ReservedView_394 a0 = ()
data T_ReservedView_394
  = C_rv'45'reserved_398 | C_rv'45'not'45'reserved_400
-- Once.Parser.ExprRelation.reserved-view
d_reserved'45'view_404 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_ReservedView_394
d_reserved'45'view_404 v0
  = let v1 = d_isReserved_6 (coe v0) in
    coe
      (if coe v1
         then coe C_rv'45'reserved_398
         else coe C_rv'45'not'45'reserved_400)
-- Once.Parser.ExprRelation.WordEqView
d_WordEqView_422 a0 a1 = ()
data T_WordEqView_422 = C_we'45'match_428 | C_we'45'nomatch_430
-- Once.Parser.ExprRelation.wordEq-view
d_wordEq'45'view_436 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_WordEqView_422
d_wordEq'45'view_436 v0 v1
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
                then coe seq (coe v4) (coe C_we'45'match_428)
                else coe seq (coe v4) (coe C_we'45'nomatch_430)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.ExprRelation.ParsesExpr
d_ParsesExpr_458 a0 a1 a2 = ()
newtype T_ParsesExpr_458 = C_pe'45'mk_508 T_ParsesComp_460
-- Once.Parser.ExprRelation.ParsesComp
d_ParsesComp_460 a0 a1 a2 = ()
data T_ParsesComp_460
  = C_pc'45'mk_520 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesCmp_464
                   T_ParsesCompTail_462
-- Once.Parser.ExprRelation.ParsesCompTail
d_ParsesCompTail_462 a0 a1 a2 a3 = ()
data T_ParsesCompTail_462
  = C_pct'45'done_526 AgdaAny |
    C_pct'45'dot_540 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesCmp_464
                     T_ParsesCompTail_462
-- Once.Parser.ExprRelation.ParsesCmp
d_ParsesCmp_464 a0 a1 a2 = ()
data T_ParsesCmp_464
  = C_pcm'45'noop_548 T_ParsesAdd_466 AgdaAny |
    C_pcm'45'lt_560 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_466 T_ParsesAdd_466 |
    C_pcm'45'le_572 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_466 T_ParsesAdd_466 |
    C_pcm'45'gt_584 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_466 T_ParsesAdd_466 |
    C_pcm'45'ge_596 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_466 T_ParsesAdd_466 |
    C_pcm'45'eq_608 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_466 T_ParsesAdd_466 |
    C_pcm'45'ne_620 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_466 T_ParsesAdd_466
-- Once.Parser.ExprRelation.ParsesAdd
d_ParsesAdd_466 a0 a1 a2 = ()
data T_ParsesAdd_466
  = C_pa'45'mk_632 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesMul_470
                   T_ParsesAddTail_468
-- Once.Parser.ExprRelation.ParsesAddTail
d_ParsesAddTail_468 a0 a1 a2 a3 = ()
data T_ParsesAddTail_468
  = C_pat'45'done_638 AgdaAny |
    C_pat'45'plus_652 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesMul_470
                      T_ParsesAddTail_468 |
    C_pat'45'minus_666 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesMul_470
                       T_ParsesAddTail_468
-- Once.Parser.ExprRelation.ParsesMul
d_ParsesMul_470 a0 a1 a2 = ()
data T_ParsesMul_470
  = C_pm'45'mk_678 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesUnary_474
                   T_ParsesMulTail_472
-- Once.Parser.ExprRelation.ParsesMulTail
d_ParsesMulTail_472 a0 a1 a2 a3 = ()
data T_ParsesMulTail_472
  = C_pmt'45'done_684 AgdaAny |
    C_pmt'45'star_698 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesUnary_474
                      T_ParsesMulTail_472 |
    C_pmt'45'slash_712 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesUnary_474
                       T_ParsesMulTail_472 |
    C_pmt'45'percent_726 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                         MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesUnary_474
                         T_ParsesMulTail_472
-- Once.Parser.ExprRelation.ParsesUnary
d_ParsesUnary_474 a0 a1 a2 = ()
data T_ParsesUnary_474
  = C_pu'45'neg_734 T_ParsesUnary_474 |
    C_pu'45'app_742 T_ParsesApp_476
-- Once.Parser.ExprRelation.ParsesApp
d_ParsesApp_476 a0 a1 a2 = ()
data T_ParsesApp_476
  = C_papp'45'mk_754 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesAtomExpr_480
                     T_ParsesAppTail_478
-- Once.Parser.ExprRelation.ParsesAppTail
d_ParsesAppTail_478 a0 a1 a2 a3 = ()
data T_ParsesAppTail_478
  = C_papp'45'done_760 T_NotAtomStart_16 |
    C_papp'45'arg_774 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_AppArgOk_142
                      T_ParsesAtomExpr_480 T_ParsesAppTail_478
-- Once.Parser.ExprRelation.ParsesAtomExpr
d_ParsesAtomExpr_480 a0 a1 a2 = ()
data T_ParsesAtomExpr_480
  = C_pae'45'unit_778 | C_pae'45'int_784 | C_pae'45'str_790 |
    C_pae'45'var_796 T_NotQualPrefix_242 | C_pae'45'qual_804 |
    C_pae'45'paren_816 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesExpr_458
                       T_ParsesParenCont_498 |
    C_pae'45'lambda_824 T_ParsesLamParams_482 |
    C_pae'45'let_832 T_ParsesLet_484 |
    C_pae'45'destruct_840 T_ParsesDestruct_488 |
    C_pae'45'paren'45'op_848 T_ParsesOpExpr_496
-- Once.Parser.ExprRelation.ParsesLamParams
d_ParsesLamParams_482 a0 a1 a2 = ()
data T_ParsesLamParams_482
  = C_plp'45'body_856 T_ParsesExpr_458 |
    C_plp'45'arg_866 T_ParsesLamParams_482
-- Once.Parser.ExprRelation.ParsesLet
d_ParsesLet_484 a0 a1 a2 = ()
data T_ParsesLet_484
  = C_plet'45'single_880 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                         MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesExpr_458
                         T_ParsesLetIn_486
-- Once.Parser.ExprRelation.ParsesLetIn
d_ParsesLetIn_486 a0 a1 a2 a3 a4 = ()
newtype T_ParsesLetIn_486 = C_plin_892 T_ParsesExpr_458
-- Once.Parser.ExprRelation.ParsesDestruct
d_ParsesDestruct_488 a0 a1 a2 = ()
data T_ParsesDestruct_488
  = C_pd'45'mk_904 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesExpr_458
                   T_ParsesDestructOf_490
-- Once.Parser.ExprRelation.ParsesDestructOf
d_ParsesDestructOf_490 a0 a1 a2 a3 = ()
newtype T_ParsesDestructOf_490
  = C_pdof_914 T_ParsesDestructBranches_492
-- Once.Parser.ExprRelation.ParsesDestructBranches
d_ParsesDestructBranches_492 a0 a1 a2 a3 = ()
data T_ParsesDestructBranches_492
  = C_pdb_930 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
              MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesExpr_458
              T_ParsesRightBranch_494
-- Once.Parser.ExprRelation.ParsesRightBranch
d_ParsesRightBranch_494 a0 a1 a2 a3 a4 a5 = ()
newtype T_ParsesRightBranch_494 = C_prb_946 T_ParsesExpr_458
-- Once.Parser.ExprRelation.ParsesOpExpr
d_ParsesOpExpr_496 a0 a1 a2 a3 = ()
data T_ParsesOpExpr_496
  = C_poe'45'close_954 | C_poe'45'dot_964 T_ParsesOpExpr_496 |
    C_poe'45'plus_974 T_ParsesOpExpr_496 |
    C_poe'45'minus_984 T_ParsesOpExpr_496 |
    C_poe'45'star_994 T_ParsesOpExpr_496 |
    C_poe'45'slash_1004 T_ParsesOpExpr_496 |
    C_poe'45'percent_1014 T_ParsesOpExpr_496 |
    C_poe'45'lt_1024 T_ParsesOpExpr_496 |
    C_poe'45'gt_1034 T_ParsesOpExpr_496 |
    C_poe'45'pipe_1044 T_ParsesOpExpr_496 |
    C_poe'45'amp_1054 T_ParsesOpExpr_496 |
    C_poe'45'at_1064 T_ParsesOpExpr_496
-- Once.Parser.ExprRelation.ParsesParenCont
d_ParsesParenCont_498 a0 a1 a2 a3 = ()
data T_ParsesParenCont_498
  = C_ppc'45'close_1070 |
    C_ppc'45'pair_1082 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       T_ParsesExpr_458 T_ParsesParenTriple_500 |
    C_ppc'45'annot_1092 MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
-- Once.Parser.ExprRelation.ParsesParenTriple
d_ParsesParenTriple_500 a0 a1 a2 a3 = ()
data T_ParsesParenTriple_500 = C_ppt'45'close_1100
-- Once.Parser.ExprRelation.ParsesExpr-shrinks
d_ParsesExpr'45'shrinks_1108 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesExpr_458 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesExpr'45'shrinks_1108 v0 ~v1 ~v2 v3
  = du_ParsesExpr'45'shrinks_1108 v0 v3
du_ParsesExpr'45'shrinks_1108 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesExpr_458 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesExpr'45'shrinks_1108 v0 v1
  = case coe v1 of
      C_pe'45'mk_508 v5
        -> coe du_ParsesComp'45'shrinks_1116 (coe v0) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesComp-shrinks
d_ParsesComp'45'shrinks_1116 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesComp_460 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesComp'45'shrinks_1116 v0 ~v1 ~v2 v3
  = du_ParsesComp'45'shrinks_1116 v0 v3
du_ParsesComp'45'shrinks_1116 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesComp_460 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesComp'45'shrinks_1116 v0 v1
  = case coe v1 of
      C_pc'45'mk_520 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesCompTail'45'shrinks_1126 (coe v3) (coe v8))
             (coe du_ParsesCmp'45'shrinks_1134 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesCompTail-shrinks
d_ParsesCompTail'45'shrinks_1126 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCompTail_462 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesCompTail'45'shrinks_1126 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesCompTail'45'shrinks_1126 v1 v4
du_ParsesCompTail'45'shrinks_1126 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCompTail_462 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesCompTail'45'shrinks_1126 v0 v1
  = case coe v1 of
      C_pct'45'done_526 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pct'45'dot_540 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesCompTail'45'shrinks_1126 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesCmp'45'shrinks_1134 (coe v11) (coe v8))
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
d_ParsesCmp'45'shrinks_1134 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCmp_464 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesCmp'45'shrinks_1134 v0 ~v1 ~v2 v3
  = du_ParsesCmp'45'shrinks_1134 v0 v3
du_ParsesCmp'45'shrinks_1134 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCmp_464 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesCmp'45'shrinks_1134 v0 v1
  = case coe v1 of
      C_pcm'45'noop_548 v5 v6
        -> coe du_ParsesAdd'45'shrinks_1142 (coe v0) (coe v5)
      C_pcm'45'lt_560 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1142 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1142 (coe v0) (coe v7)))
      C_pcm'45'le_572 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1142 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1142 (coe v0) (coe v7)))
      C_pcm'45'gt_584 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1142 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1142 (coe v0) (coe v7)))
      C_pcm'45'ge_596 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1142 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1142 (coe v0) (coe v7)))
      C_pcm'45'eq_608 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1142 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1142 (coe v0) (coe v7)))
      C_pcm'45'ne_620 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1142 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1142 (coe v0) (coe v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAdd-shrinks
d_ParsesAdd'45'shrinks_1142 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAdd_466 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAdd'45'shrinks_1142 v0 ~v1 ~v2 v3
  = du_ParsesAdd'45'shrinks_1142 v0 v3
du_ParsesAdd'45'shrinks_1142 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAdd_466 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAdd'45'shrinks_1142 v0 v1
  = case coe v1 of
      C_pa'45'mk_632 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesAddTail'45'shrinks_1152 (coe v3) (coe v8))
             (coe du_ParsesMul'45'shrinks_1160 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAddTail-shrinks
d_ParsesAddTail'45'shrinks_1152 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAddTail_468 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAddTail'45'shrinks_1152 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesAddTail'45'shrinks_1152 v1 v4
du_ParsesAddTail'45'shrinks_1152 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAddTail_468 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAddTail'45'shrinks_1152 v0 v1
  = case coe v1 of
      C_pat'45'done_638 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pat'45'plus_652 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1152 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesMul'45'shrinks_1160 (coe v11) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pat'45'minus_666 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1152 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesMul'45'shrinks_1160 (coe v11) (coe v8))
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
d_ParsesMul'45'shrinks_1160 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMul_470 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesMul'45'shrinks_1160 v0 ~v1 ~v2 v3
  = du_ParsesMul'45'shrinks_1160 v0 v3
du_ParsesMul'45'shrinks_1160 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMul_470 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesMul'45'shrinks_1160 v0 v1
  = case coe v1 of
      C_pm'45'mk_678 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesMulTail'45'shrinks_1170 (coe v3) (coe v8))
             (coe du_ParsesUnary'45'shrinks_1178 (coe v0) (coe v5) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesMulTail-shrinks
d_ParsesMulTail'45'shrinks_1170 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMulTail_472 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesMulTail'45'shrinks_1170 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesMulTail'45'shrinks_1170 v1 v4
du_ParsesMulTail'45'shrinks_1170 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMulTail_472 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesMulTail'45'shrinks_1170 v0 v1
  = case coe v1 of
      C_pmt'45'done_684 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pmt'45'star_698 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1170 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1178 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'slash_712 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1170 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1178 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'percent_726 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1170 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1178 (coe v11) (coe v6) (coe v8))
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
d_ParsesUnary'45'shrinks_1178 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesUnary_474 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesUnary'45'shrinks_1178 v0 v1 ~v2 v3
  = du_ParsesUnary'45'shrinks_1178 v0 v1 v3
du_ParsesUnary'45'shrinks_1178 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_ParsesUnary_474 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesUnary'45'shrinks_1178 v0 v1 v2
  = case coe v2 of
      C_pu'45'neg_734 v6
        -> case coe v0 of
             (:) v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_62 v10
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v8)
                           (coe du_ParsesUnary'45'shrinks_1178 (coe v8) (coe v10) (coe v6))
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
      C_pu'45'app_742 v6
        -> coe du_ParsesApp'45'shrinks_1186 (coe v0) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesApp-shrinks
d_ParsesApp'45'shrinks_1186 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesApp_476 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesApp'45'shrinks_1186 v0 ~v1 ~v2 v3
  = du_ParsesApp'45'shrinks_1186 v0 v3
du_ParsesApp'45'shrinks_1186 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesApp_476 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesApp'45'shrinks_1186 v0 v1
  = case coe v1 of
      C_papp'45'mk_754 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesAppTail'45'shrinks_1196 (coe v3) (coe v8))
             (coe
                d_ParsesAtomExpr'45'shrinks_1204 (coe v0) (coe v5) (coe v3)
                (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAppTail-shrinks
d_ParsesAppTail'45'shrinks_1196 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAppTail_478 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAppTail'45'shrinks_1196 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesAppTail'45'shrinks_1196 v1 v4
du_ParsesAppTail'45'shrinks_1196 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAppTail_478 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAppTail'45'shrinks_1196 v0 v1
  = case coe v1 of
      C_papp'45'done_760 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_papp'45'arg_774 v4 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe du_ParsesAppTail'45'shrinks_1196 (coe v4) (coe v10))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                (coe
                   d_ParsesAtomExpr'45'shrinks_1204 (coe v0) (coe v6) (coe v4)
                   (coe v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAtomExpr-shrinks
d_ParsesAtomExpr'45'shrinks_1204 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAtomExpr_480 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAtomExpr'45'shrinks_1204 v0 v1 v2 v3
  = case coe v3 of
      C_pae'45'unit_778
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'int_784
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'str_790
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'var_796 v7
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                    coe (coe (\ v9 -> v8)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'qual_804
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                    coe (coe (\ v9 -> v8)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'paren_816 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
                    (coe
                       du_ParsesParenCont'45'shrinks_1294 (coe v5) (coe v1) (coe v2)
                       (coe v10))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                       (coe du_ParsesExpr'45'shrinks_1108 (coe v12) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                 coe (coe (\ v14 -> v13)))
                                (coe (0 :: Integer)) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'lambda_824 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesLamParams'45'shrinks_1222 (coe v9) (coe v1) (coe v2)
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
      C_pae'45'let_832 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesLet'45'shrinks_1230 (coe v9) (coe v1) (coe v2) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'destruct_840 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesDestruct'45'shrinks_1250 (coe v9) (coe v1) (coe v2)
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
      C_pae'45'paren'45'op_848 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v2) (coe v7))
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
d_ParsesOpExpr'45'shrinks_1214 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesOpExpr_496 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesOpExpr'45'shrinks_1214 ~v0 v1 ~v2 v3 v4
  = du_ParsesOpExpr'45'shrinks_1214 v1 v3 v4
du_ParsesOpExpr'45'shrinks_1214 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesOpExpr_496 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesOpExpr'45'shrinks_1214 v0 v1 v2
  = case coe v2 of
      C_poe'45'close_954
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v1)))
      C_poe'45'dot_964 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'plus_974 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'minus_984 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'star_994 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'slash_1004 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'percent_1014 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'lt_1024 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'gt_1034 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'pipe_1044 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'amp_1054 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'at_1064 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1214 (coe v9) (coe v1) (coe v7))
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
d_ParsesLamParams'45'shrinks_1222 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLamParams_482 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLamParams'45'shrinks_1222 v0 v1 v2 v3
  = case coe v3 of
      C_plp'45'body_856 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesExpr'45'shrinks_1108 (coe v9) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_plp'45'arg_866 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v11 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                           (coe
                              d_ParsesLamParams'45'shrinks_1222 (coe v10) (coe v12) (coe v2)
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
d_ParsesLet'45'shrinks_1230 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLet_484 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLet'45'shrinks_1230 v0 v1 v2 v3
  = case coe v3 of
      C_plet'45'single_880 v6 v8 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                           (coe
                              du_ParsesLetIn'45'shrinks_1242 (coe v6) (coe v1) (coe v2)
                              (coe v11))
                           (coe du_ParsesExpr'45'shrinks_1108 (coe v15) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesLetIn-shrinks
d_ParsesLetIn'45'shrinks_1242 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLetIn_486 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLetIn'45'shrinks_1242 ~v0 ~v1 v2 v3 v4 v5
  = du_ParsesLetIn'45'shrinks_1242 v2 v3 v4 v5
du_ParsesLetIn'45'shrinks_1242 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLetIn_486 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesLetIn'45'shrinks_1242 v0 v1 v2 v3
  = case coe v3 of
      C_plin_892 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                           (coe du_ParsesExpr'45'shrinks_1108 (coe v11) (coe v9))
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
d_ParsesDestruct'45'shrinks_1250 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestruct_488 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestruct'45'shrinks_1250 v0 v1 v2 v3
  = case coe v3 of
      C_pd'45'mk_904 v5 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
             (coe
                du_ParsesDestructOf'45'shrinks_1260 (coe v5) (coe v1) (coe v2)
                (coe v10))
             (coe du_ParsesExpr'45'shrinks_1108 (coe v0) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestructOf-shrinks
d_ParsesDestructOf'45'shrinks_1260 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructOf_490 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestructOf'45'shrinks_1260 ~v0 v1 v2 v3 v4
  = du_ParsesDestructOf'45'shrinks_1260 v1 v2 v3 v4
du_ParsesDestructOf'45'shrinks_1260 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructOf_490 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesDestructOf'45'shrinks_1260 v0 v1 v2 v3
  = case coe v3 of
      C_pdof_914 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> coe
                           du_ParsesDestructBranches'45'shrinks_1270 (coe v12) (coe v1)
                           (coe v2) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestructBranches-shrinks
d_ParsesDestructBranches'45'shrinks_1270 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructBranches_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestructBranches'45'shrinks_1270 ~v0 v1 v2 v3 v4
  = du_ParsesDestructBranches'45'shrinks_1270 v1 v2 v3 v4
du_ParsesDestructBranches'45'shrinks_1270 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructBranches_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesDestructBranches'45'shrinks_1270 v0 v1 v2 v3
  = case coe v3 of
      C_pdb_930 v7 v8 v11 v12
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
                                     du_ParsesRightBranch'45'shrinks_1284 (coe v7) (coe v1) (coe v2)
                                     (coe v12))
                                  (coe du_ParsesExpr'45'shrinks_1108 (coe v18) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesRightBranch-shrinks
d_ParsesRightBranch'45'shrinks_1284 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesRightBranch_494 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesRightBranch'45'shrinks_1284 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_ParsesRightBranch'45'shrinks_1284 v3 v4 v5 v6
du_ParsesRightBranch'45'shrinks_1284 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesRightBranch_494 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesRightBranch'45'shrinks_1284 v0 v1 v2 v3
  = case coe v3 of
      C_prb_946 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> case coe v15 of
                           (:) v16 v17
                             -> case coe v17 of
                                  (:) v18 v19
                                    -> case coe v1 of
                                         MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v20 v21 v22 v23 v24
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
                                                   du_ParsesExpr'45'shrinks_1108 (coe v19)
                                                   (coe v11))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesParenCont-shrinks
d_ParsesParenCont'45'shrinks_1294 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenCont_498 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesParenCont'45'shrinks_1294 ~v0 v1 v2 v3 v4
  = du_ParsesParenCont'45'shrinks_1294 v1 v2 v3 v4
du_ParsesParenCont'45'shrinks_1294 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenCont_498 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesParenCont'45'shrinks_1294 v0 v1 v2 v3
  = case coe v3 of
      C_ppc'45'close_1070
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v2)))
      C_ppc'45'pair_1082 v6 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                           (coe du_ParsesParenTriple'45'shrinks_1304 (coe v2) (coe v10))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                              (coe du_ParsesExpr'45'shrinks_1108 (coe v12) (coe v9))
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
      C_ppc'45'annot_1092 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_58 v11 v12
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
                                 MAlonzo.Code.Once.Parser.TypeRelation.d_ParsesType'45'shrinks_432
                                 (coe v10) (coe v12)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_16) (coe v2))
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
d_ParsesParenTriple'45'shrinks_1304 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenTriple_500 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesParenTriple'45'shrinks_1304 ~v0 ~v1 ~v2 v3 v4
  = du_ParsesParenTriple'45'shrinks_1304 v3 v4
du_ParsesParenTriple'45'shrinks_1304 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenTriple_500 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesParenTriple'45'shrinks_1304 v0 v1
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
