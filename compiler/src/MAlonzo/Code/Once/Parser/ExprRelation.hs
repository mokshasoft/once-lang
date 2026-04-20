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
    C_nas'45'TNewline_132 | C_nas'45'TEOF_136
-- Once.Parser.ExprRelation.AppArgOk
d_AppArgOk_138 a0 = ()
data T_AppArgOk_138
  = C_aao'45'TLParen_142 | C_aao'45'TLambda_146 | C_aao'45'TInt_152 |
    C_aao'45'TString_158 | C_aao'45'word_164
-- Once.Parser.ExprRelation.NotTWord
d_NotTWord_166 a0 = ()
data T_NotTWord_166
  = C_ntw'45'TLParen_168 | C_ntw'45'TRParen_170 |
    C_ntw'45'TLBrace_172 | C_ntw'45'TRBrace_174 | C_ntw'45'TColon_176 |
    C_ntw'45'TEquals_178 | C_ntw'45'TArrow_180 | C_ntw'45'TCaret0_182 |
    C_ntw'45'TCaret1_184 | C_ntw'45'TCaretW_186 |
    C_ntw'45'TLambda_188 | C_ntw'45'TComma_190 |
    C_ntw'45'TSemicolon_192 | C_ntw'45'TAt_194 | C_ntw'45'TPipe_196 |
    C_ntw'45'TDot_198 | C_ntw'45'TPlus_200 | C_ntw'45'TMinus_202 |
    C_ntw'45'TStar_204 | C_ntw'45'TSlash_206 | C_ntw'45'TPercent_208 |
    C_ntw'45'TAmpersand_210 | C_ntw'45'TLt_212 | C_ntw'45'TLe_214 |
    C_ntw'45'TGt_216 | C_ntw'45'TGe_218 | C_ntw'45'TEqEq_220 |
    C_ntw'45'TNeq_222 | C_ntw'45'TNewline_224 | C_ntw'45'TEOF_226 |
    C_ntw'45'TInt_230 | C_ntw'45'TString_234
-- Once.Parser.ExprRelation.NotQualPrefix
d_NotQualPrefix_236 a0 = ()
data T_NotQualPrefix_236
  = C_nqp'45''91''93'_238 | C_nqp'45'TLParen_242 |
    C_nqp'45'TRParen_246 | C_nqp'45'TLBrace_250 |
    C_nqp'45'TRBrace_254 | C_nqp'45'TColon_258 | C_nqp'45'TEquals_262 |
    C_nqp'45'TArrow_266 | C_nqp'45'TCaret0_270 | C_nqp'45'TCaret1_274 |
    C_nqp'45'TCaretW_278 | C_nqp'45'TLambda_282 | C_nqp'45'TComma_286 |
    C_nqp'45'TSemicolon_290 | C_nqp'45'TPipe_294 | C_nqp'45'TDot_298 |
    C_nqp'45'TPlus_302 | C_nqp'45'TMinus_306 | C_nqp'45'TStar_310 |
    C_nqp'45'TSlash_314 | C_nqp'45'TPercent_318 |
    C_nqp'45'TAmpersand_322 | C_nqp'45'TLt_326 | C_nqp'45'TLe_330 |
    C_nqp'45'TGt_334 | C_nqp'45'TGe_338 | C_nqp'45'TEqEq_342 |
    C_nqp'45'TNeq_346 | C_nqp'45'TNewline_350 | C_nqp'45'TEOF_354 |
    C_nqp'45'TWord_360 | C_nqp'45'TInt_366 | C_nqp'45'TString_372 |
    C_nqp'45'TAt'45''91''93'_374 |
    C_nqp'45'TAt'45'cons_380 T_NotTWord_166
-- Once.Parser.ExprRelation.ReservedView
d_ReservedView_384 a0 = ()
data T_ReservedView_384
  = C_rv'45'reserved_388 | C_rv'45'not'45'reserved_390
-- Once.Parser.ExprRelation.reserved-view
d_reserved'45'view_394 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_ReservedView_384
d_reserved'45'view_394 v0
  = let v1 = d_isReserved_6 (coe v0) in
    coe
      (if coe v1
         then coe C_rv'45'reserved_388
         else coe C_rv'45'not'45'reserved_390)
-- Once.Parser.ExprRelation.WordEqView
d_WordEqView_412 a0 a1 = ()
data T_WordEqView_412 = C_we'45'match_418 | C_we'45'nomatch_420
-- Once.Parser.ExprRelation.wordEq-view
d_wordEq'45'view_426 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_WordEqView_412
d_wordEq'45'view_426 v0 v1
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
                then coe seq (coe v4) (coe C_we'45'match_418)
                else coe seq (coe v4) (coe C_we'45'nomatch_420)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.ExprRelation.ParsesExpr
d_ParsesExpr_448 a0 a1 a2 = ()
newtype T_ParsesExpr_448 = C_pe'45'mk_498 T_ParsesComp_450
-- Once.Parser.ExprRelation.ParsesComp
d_ParsesComp_450 a0 a1 a2 = ()
data T_ParsesComp_450
  = C_pc'45'mk_510 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesCmp_454
                   T_ParsesCompTail_452
-- Once.Parser.ExprRelation.ParsesCompTail
d_ParsesCompTail_452 a0 a1 a2 a3 = ()
data T_ParsesCompTail_452
  = C_pct'45'done_516 AgdaAny |
    C_pct'45'dot_530 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesCmp_454
                     T_ParsesCompTail_452
-- Once.Parser.ExprRelation.ParsesCmp
d_ParsesCmp_454 a0 a1 a2 = ()
data T_ParsesCmp_454
  = C_pcm'45'noop_538 T_ParsesAdd_456 AgdaAny |
    C_pcm'45'lt_550 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_456 T_ParsesAdd_456 |
    C_pcm'45'le_562 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_456 T_ParsesAdd_456 |
    C_pcm'45'gt_574 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_456 T_ParsesAdd_456 |
    C_pcm'45'ge_586 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_456 T_ParsesAdd_456 |
    C_pcm'45'eq_598 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_456 T_ParsesAdd_456 |
    C_pcm'45'ne_610 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    T_ParsesAdd_456 T_ParsesAdd_456
-- Once.Parser.ExprRelation.ParsesAdd
d_ParsesAdd_456 a0 a1 a2 = ()
data T_ParsesAdd_456
  = C_pa'45'mk_622 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesMul_460
                   T_ParsesAddTail_458
-- Once.Parser.ExprRelation.ParsesAddTail
d_ParsesAddTail_458 a0 a1 a2 a3 = ()
data T_ParsesAddTail_458
  = C_pat'45'done_628 AgdaAny |
    C_pat'45'plus_642 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesMul_460
                      T_ParsesAddTail_458 |
    C_pat'45'minus_656 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesMul_460
                       T_ParsesAddTail_458
-- Once.Parser.ExprRelation.ParsesMul
d_ParsesMul_460 a0 a1 a2 = ()
data T_ParsesMul_460
  = C_pm'45'mk_668 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesUnary_464
                   T_ParsesMulTail_462
-- Once.Parser.ExprRelation.ParsesMulTail
d_ParsesMulTail_462 a0 a1 a2 a3 = ()
data T_ParsesMulTail_462
  = C_pmt'45'done_674 AgdaAny |
    C_pmt'45'star_688 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesUnary_464
                      T_ParsesMulTail_462 |
    C_pmt'45'slash_702 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesUnary_464
                       T_ParsesMulTail_462 |
    C_pmt'45'percent_716 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                         MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesUnary_464
                         T_ParsesMulTail_462
-- Once.Parser.ExprRelation.ParsesUnary
d_ParsesUnary_464 a0 a1 a2 = ()
data T_ParsesUnary_464
  = C_pu'45'neg_724 T_ParsesUnary_464 |
    C_pu'45'app_732 T_ParsesApp_466
-- Once.Parser.ExprRelation.ParsesApp
d_ParsesApp_466 a0 a1 a2 = ()
data T_ParsesApp_466
  = C_papp'45'mk_744 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesAtomExpr_470
                     T_ParsesAppTail_468
-- Once.Parser.ExprRelation.ParsesAppTail
d_ParsesAppTail_468 a0 a1 a2 a3 = ()
data T_ParsesAppTail_468
  = C_papp'45'done_750 T_NotAtomStart_16 |
    C_papp'45'arg_764 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                      MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_AppArgOk_138
                      T_ParsesAtomExpr_470 T_ParsesAppTail_468
-- Once.Parser.ExprRelation.ParsesAtomExpr
d_ParsesAtomExpr_470 a0 a1 a2 = ()
data T_ParsesAtomExpr_470
  = C_pae'45'unit_768 | C_pae'45'int_774 | C_pae'45'str_780 |
    C_pae'45'var_786 T_NotQualPrefix_236 | C_pae'45'qual_794 |
    C_pae'45'paren_806 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesExpr_448
                       T_ParsesParenCont_488 |
    C_pae'45'lambda_814 T_ParsesLamParams_472 |
    C_pae'45'let_822 T_ParsesLet_474 |
    C_pae'45'destruct_830 T_ParsesDestruct_478 |
    C_pae'45'paren'45'op_838 T_ParsesOpExpr_486
-- Once.Parser.ExprRelation.ParsesLamParams
d_ParsesLamParams_472 a0 a1 a2 = ()
data T_ParsesLamParams_472
  = C_plp'45'body_846 T_ParsesExpr_448 |
    C_plp'45'arg_856 T_ParsesLamParams_472
-- Once.Parser.ExprRelation.ParsesLet
d_ParsesLet_474 a0 a1 a2 = ()
data T_ParsesLet_474
  = C_plet'45'single_870 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                         MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesExpr_448
                         T_ParsesLetIn_476
-- Once.Parser.ExprRelation.ParsesLetIn
d_ParsesLetIn_476 a0 a1 a2 a3 a4 = ()
newtype T_ParsesLetIn_476 = C_plin_882 T_ParsesExpr_448
-- Once.Parser.ExprRelation.ParsesDestruct
d_ParsesDestruct_478 a0 a1 a2 = ()
data T_ParsesDestruct_478
  = C_pd'45'mk_894 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesExpr_448
                   T_ParsesDestructOf_480
-- Once.Parser.ExprRelation.ParsesDestructOf
d_ParsesDestructOf_480 a0 a1 a2 a3 = ()
newtype T_ParsesDestructOf_480
  = C_pdof_904 T_ParsesDestructBranches_482
-- Once.Parser.ExprRelation.ParsesDestructBranches
d_ParsesDestructBranches_482 a0 a1 a2 a3 = ()
data T_ParsesDestructBranches_482
  = C_pdb_920 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
              MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 T_ParsesExpr_448
              T_ParsesRightBranch_484
-- Once.Parser.ExprRelation.ParsesRightBranch
d_ParsesRightBranch_484 a0 a1 a2 a3 a4 a5 = ()
newtype T_ParsesRightBranch_484 = C_prb_936 T_ParsesExpr_448
-- Once.Parser.ExprRelation.ParsesOpExpr
d_ParsesOpExpr_486 a0 a1 a2 a3 = ()
data T_ParsesOpExpr_486
  = C_poe'45'close_944 | C_poe'45'dot_954 T_ParsesOpExpr_486 |
    C_poe'45'plus_964 T_ParsesOpExpr_486 |
    C_poe'45'minus_974 T_ParsesOpExpr_486 |
    C_poe'45'star_984 T_ParsesOpExpr_486 |
    C_poe'45'slash_994 T_ParsesOpExpr_486 |
    C_poe'45'percent_1004 T_ParsesOpExpr_486 |
    C_poe'45'lt_1014 T_ParsesOpExpr_486 |
    C_poe'45'gt_1024 T_ParsesOpExpr_486 |
    C_poe'45'pipe_1034 T_ParsesOpExpr_486 |
    C_poe'45'amp_1044 T_ParsesOpExpr_486 |
    C_poe'45'at_1054 T_ParsesOpExpr_486
-- Once.Parser.ExprRelation.ParsesParenCont
d_ParsesParenCont_488 a0 a1 a2 a3 = ()
data T_ParsesParenCont_488
  = C_ppc'45'close_1060 |
    C_ppc'45'pair_1072 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                       T_ParsesExpr_448 T_ParsesParenTriple_490 |
    C_ppc'45'annot_1082 MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106
-- Once.Parser.ExprRelation.ParsesParenTriple
d_ParsesParenTriple_490 a0 a1 a2 a3 = ()
data T_ParsesParenTriple_490 = C_ppt'45'close_1090
-- Once.Parser.ExprRelation.ParsesExpr-shrinks
d_ParsesExpr'45'shrinks_1098 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesExpr_448 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesExpr'45'shrinks_1098 v0 ~v1 ~v2 v3
  = du_ParsesExpr'45'shrinks_1098 v0 v3
du_ParsesExpr'45'shrinks_1098 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesExpr_448 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesExpr'45'shrinks_1098 v0 v1
  = case coe v1 of
      C_pe'45'mk_498 v5
        -> coe du_ParsesComp'45'shrinks_1106 (coe v0) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesComp-shrinks
d_ParsesComp'45'shrinks_1106 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesComp_450 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesComp'45'shrinks_1106 v0 ~v1 ~v2 v3
  = du_ParsesComp'45'shrinks_1106 v0 v3
du_ParsesComp'45'shrinks_1106 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesComp_450 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesComp'45'shrinks_1106 v0 v1
  = case coe v1 of
      C_pc'45'mk_510 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesCompTail'45'shrinks_1116 (coe v3) (coe v8))
             (coe du_ParsesCmp'45'shrinks_1124 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesCompTail-shrinks
d_ParsesCompTail'45'shrinks_1116 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCompTail_452 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesCompTail'45'shrinks_1116 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesCompTail'45'shrinks_1116 v1 v4
du_ParsesCompTail'45'shrinks_1116 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCompTail_452 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesCompTail'45'shrinks_1116 v0 v1
  = case coe v1 of
      C_pct'45'done_516 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pct'45'dot_530 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesCompTail'45'shrinks_1116 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesCmp'45'shrinks_1124 (coe v11) (coe v8))
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
d_ParsesCmp'45'shrinks_1124 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCmp_454 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesCmp'45'shrinks_1124 v0 ~v1 ~v2 v3
  = du_ParsesCmp'45'shrinks_1124 v0 v3
du_ParsesCmp'45'shrinks_1124 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesCmp_454 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesCmp'45'shrinks_1124 v0 v1
  = case coe v1 of
      C_pcm'45'noop_538 v5 v6
        -> coe du_ParsesAdd'45'shrinks_1132 (coe v0) (coe v5)
      C_pcm'45'lt_550 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1132 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1132 (coe v0) (coe v7)))
      C_pcm'45'le_562 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1132 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1132 (coe v0) (coe v7)))
      C_pcm'45'gt_574 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1132 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1132 (coe v0) (coe v7)))
      C_pcm'45'ge_586 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1132 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1132 (coe v0) (coe v7)))
      C_pcm'45'eq_598 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1132 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1132 (coe v0) (coe v7)))
      C_pcm'45'ne_610 v3 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)
             (coe du_ParsesAdd'45'shrinks_1132 (coe v3) (coe v8))
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
                (coe du_ParsesAdd'45'shrinks_1132 (coe v0) (coe v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAdd-shrinks
d_ParsesAdd'45'shrinks_1132 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAdd_456 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAdd'45'shrinks_1132 v0 ~v1 ~v2 v3
  = du_ParsesAdd'45'shrinks_1132 v0 v3
du_ParsesAdd'45'shrinks_1132 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAdd_456 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAdd'45'shrinks_1132 v0 v1
  = case coe v1 of
      C_pa'45'mk_622 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesAddTail'45'shrinks_1142 (coe v3) (coe v8))
             (coe du_ParsesMul'45'shrinks_1150 (coe v0) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAddTail-shrinks
d_ParsesAddTail'45'shrinks_1142 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAddTail_458 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAddTail'45'shrinks_1142 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesAddTail'45'shrinks_1142 v1 v4
du_ParsesAddTail'45'shrinks_1142 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAddTail_458 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAddTail'45'shrinks_1142 v0 v1
  = case coe v1 of
      C_pat'45'done_628 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pat'45'plus_642 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1142 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesMul'45'shrinks_1150 (coe v11) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pat'45'minus_656 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesAddTail'45'shrinks_1142 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesMul'45'shrinks_1150 (coe v11) (coe v8))
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
d_ParsesMul'45'shrinks_1150 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMul_460 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesMul'45'shrinks_1150 v0 ~v1 ~v2 v3
  = du_ParsesMul'45'shrinks_1150 v0 v3
du_ParsesMul'45'shrinks_1150 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMul_460 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesMul'45'shrinks_1150 v0 v1
  = case coe v1 of
      C_pm'45'mk_668 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesMulTail'45'shrinks_1160 (coe v3) (coe v8))
             (coe du_ParsesUnary'45'shrinks_1168 (coe v0) (coe v5) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesMulTail-shrinks
d_ParsesMulTail'45'shrinks_1160 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMulTail_462 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesMulTail'45'shrinks_1160 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesMulTail'45'shrinks_1160 v1 v4
du_ParsesMulTail'45'shrinks_1160 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesMulTail_462 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesMulTail'45'shrinks_1160 v0 v1
  = case coe v1 of
      C_pmt'45'done_674 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_pmt'45'star_688 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1160 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1168 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'slash_702 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1160 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1168 (coe v11) (coe v6) (coe v8))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v12 = \ v12 -> addInt (coe (1 :: Integer)) (coe v12) in
                                    coe (coe (\ v13 -> v12)))
                                   (coe (0 :: Integer)) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmt'45'percent_716 v4 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe du_ParsesMulTail'45'shrinks_1160 (coe v4) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                          (coe du_ParsesUnary'45'shrinks_1168 (coe v11) (coe v6) (coe v8))
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
d_ParsesUnary'45'shrinks_1168 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesUnary_464 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesUnary'45'shrinks_1168 v0 v1 ~v2 v3
  = du_ParsesUnary'45'shrinks_1168 v0 v1 v3
du_ParsesUnary'45'shrinks_1168 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_ParsesUnary_464 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesUnary'45'shrinks_1168 v0 v1 v2
  = case coe v2 of
      C_pu'45'neg_724 v6
        -> case coe v0 of
             (:) v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v10
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v8)
                           (coe du_ParsesUnary'45'shrinks_1168 (coe v8) (coe v10) (coe v6))
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
      C_pu'45'app_732 v6
        -> coe du_ParsesApp'45'shrinks_1176 (coe v0) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesApp-shrinks
d_ParsesApp'45'shrinks_1176 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesApp_466 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesApp'45'shrinks_1176 v0 ~v1 ~v2 v3
  = du_ParsesApp'45'shrinks_1176 v0 v3
du_ParsesApp'45'shrinks_1176 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesApp_466 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesApp'45'shrinks_1176 v0 v1
  = case coe v1 of
      C_papp'45'mk_744 v3 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
             (coe du_ParsesAppTail'45'shrinks_1186 (coe v3) (coe v8))
             (coe
                d_ParsesAtomExpr'45'shrinks_1194 (coe v0) (coe v5) (coe v3)
                (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAppTail-shrinks
d_ParsesAppTail'45'shrinks_1186 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAppTail_468 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAppTail'45'shrinks_1186 ~v0 v1 ~v2 ~v3 v4
  = du_ParsesAppTail'45'shrinks_1186 v1 v4
du_ParsesAppTail'45'shrinks_1186 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAppTail_468 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesAppTail'45'shrinks_1186 v0 v1
  = case coe v1 of
      C_papp'45'done_750 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
      C_papp'45'arg_764 v4 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe du_ParsesAppTail'45'shrinks_1186 (coe v4) (coe v10))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                (coe
                   d_ParsesAtomExpr'45'shrinks_1194 (coe v0) (coe v6) (coe v4)
                   (coe v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesAtomExpr-shrinks
d_ParsesAtomExpr'45'shrinks_1194 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesAtomExpr_470 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesAtomExpr'45'shrinks_1194 v0 v1 v2 v3
  = case coe v3 of
      C_pae'45'unit_768
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                    coe (coe (\ v6 -> v5)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'int_774
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'str_780
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'var_786 v7
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                    coe (coe (\ v9 -> v8)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'qual_794
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                    coe (coe (\ v9 -> v8)))
                   (coe (0 :: Integer)) (coe v2)))
      C_pae'45'paren_806 v5 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
                    (coe
                       du_ParsesParenCont'45'shrinks_1284 (coe v5) (coe v1) (coe v2)
                       (coe v10))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                       (coe du_ParsesExpr'45'shrinks_1098 (coe v12) (coe v9))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (let v13 = \ v13 -> addInt (coe (1 :: Integer)) (coe v13) in
                                 coe (coe (\ v14 -> v13)))
                                (coe (0 :: Integer)) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'lambda_814 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesLamParams'45'shrinks_1212 (coe v9) (coe v1) (coe v2)
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
      C_pae'45'let_822 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesLet'45'shrinks_1220 (coe v9) (coe v1) (coe v2) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pae'45'destruct_830 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe
                       d_ParsesDestruct'45'shrinks_1240 (coe v9) (coe v1) (coe v2)
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
      C_pae'45'paren'45'op_838 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v2) (coe v7))
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
d_ParsesOpExpr'45'shrinks_1204 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesOpExpr_486 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesOpExpr'45'shrinks_1204 ~v0 v1 ~v2 v3 v4
  = du_ParsesOpExpr'45'shrinks_1204 v1 v3 v4
du_ParsesOpExpr'45'shrinks_1204 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesOpExpr_486 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesOpExpr'45'shrinks_1204 v0 v1 v2
  = case coe v2 of
      C_poe'45'close_944
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v1)))
      C_poe'45'dot_954 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'plus_964 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'minus_974 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'star_984 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'slash_994 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'percent_1004 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'lt_1014 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'gt_1024 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'pipe_1034 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'amp_1044 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poe'45'at_1054 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesOpExpr'45'shrinks_1204 (coe v9) (coe v1) (coe v7))
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
d_ParsesLamParams'45'shrinks_1212 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLamParams_472 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLamParams'45'shrinks_1212 v0 v1 v2 v3
  = case coe v3 of
      C_plp'45'body_846 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v9)
                    (coe du_ParsesExpr'45'shrinks_1098 (coe v9) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (let v10 = \ v10 -> addInt (coe (1 :: Integer)) (coe v10) in
                              coe (coe (\ v11 -> v10)))
                             (coe (0 :: Integer)) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_plp'45'arg_856 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v11 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v10)
                           (coe
                              d_ParsesLamParams'45'shrinks_1212 (coe v10) (coe v12) (coe v2)
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
d_ParsesLet'45'shrinks_1220 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLet_474 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLet'45'shrinks_1220 v0 v1 v2 v3
  = case coe v3 of
      C_plet'45'single_870 v6 v8 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                           (coe
                              du_ParsesLetIn'45'shrinks_1232 (coe v6) (coe v1) (coe v2)
                              (coe v11))
                           (coe du_ParsesExpr'45'shrinks_1098 (coe v15) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesLetIn-shrinks
d_ParsesLetIn'45'shrinks_1232 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLetIn_476 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesLetIn'45'shrinks_1232 ~v0 ~v1 v2 v3 v4 v5
  = du_ParsesLetIn'45'shrinks_1232 v2 v3 v4 v5
du_ParsesLetIn'45'shrinks_1232 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesLetIn_476 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesLetIn'45'shrinks_1232 v0 v1 v2 v3
  = case coe v3 of
      C_plin_882 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v11)
                           (coe du_ParsesExpr'45'shrinks_1098 (coe v11) (coe v9))
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
d_ParsesDestruct'45'shrinks_1240 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestruct_478 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestruct'45'shrinks_1240 v0 v1 v2 v3
  = case coe v3 of
      C_pd'45'mk_894 v5 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)
             (coe
                du_ParsesDestructOf'45'shrinks_1250 (coe v5) (coe v1) (coe v2)
                (coe v10))
             (coe du_ParsesExpr'45'shrinks_1098 (coe v0) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestructOf-shrinks
d_ParsesDestructOf'45'shrinks_1250 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructOf_480 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestructOf'45'shrinks_1250 ~v0 v1 v2 v3 v4
  = du_ParsesDestructOf'45'shrinks_1250 v1 v2 v3 v4
du_ParsesDestructOf'45'shrinks_1250 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructOf_480 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesDestructOf'45'shrinks_1250 v0 v1 v2 v3
  = case coe v3 of
      C_pdof_904 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> coe
                           du_ParsesDestructBranches'45'shrinks_1260 (coe v12) (coe v1)
                           (coe v2) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesDestructBranches-shrinks
d_ParsesDestructBranches'45'shrinks_1260 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructBranches_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesDestructBranches'45'shrinks_1260 ~v0 v1 v2 v3 v4
  = du_ParsesDestructBranches'45'shrinks_1260 v1 v2 v3 v4
du_ParsesDestructBranches'45'shrinks_1260 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDestructBranches_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesDestructBranches'45'shrinks_1260 v0 v1 v2 v3
  = case coe v3 of
      C_pdb_920 v7 v8 v11 v12
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
                                     du_ParsesRightBranch'45'shrinks_1274 (coe v7) (coe v1) (coe v2)
                                     (coe v12))
                                  (coe du_ParsesExpr'45'shrinks_1098 (coe v18) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesRightBranch-shrinks
d_ParsesRightBranch'45'shrinks_1274 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesRightBranch_484 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesRightBranch'45'shrinks_1274 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_ParsesRightBranch'45'shrinks_1274 v3 v4 v5 v6
du_ParsesRightBranch'45'shrinks_1274 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesRightBranch_484 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesRightBranch'45'shrinks_1274 v0 v1 v2 v3
  = case coe v3 of
      C_prb_936 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> case coe v15 of
                           (:) v16 v17
                             -> case coe v17 of
                                  (:) v18 v19
                                    -> case coe v1 of
                                         MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v20 v21 v22 v23 v24
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
                                                   du_ParsesExpr'45'shrinks_1098 (coe v19)
                                                   (coe v11))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ExprRelation.ParsesParenCont-shrinks
d_ParsesParenCont'45'shrinks_1284 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenCont_488 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesParenCont'45'shrinks_1284 ~v0 v1 v2 v3 v4
  = du_ParsesParenCont'45'shrinks_1284 v1 v2 v3 v4
du_ParsesParenCont'45'shrinks_1284 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenCont_488 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesParenCont'45'shrinks_1284 v0 v1 v2 v3
  = case coe v3 of
      C_ppc'45'close_1060
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
                    coe (coe (\ v7 -> v6)))
                   (coe (0 :: Integer)) (coe v2)))
      C_ppc'45'pair_1072 v6 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v13 v14
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)
                           (coe du_ParsesParenTriple'45'shrinks_1294 (coe v2) (coe v10))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v12)
                              (coe du_ParsesExpr'45'shrinks_1098 (coe v12) (coe v9))
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
      C_ppc'45'annot_1082 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v11 v12
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
                                 MAlonzo.Code.Once.Parser.TypeRelation.d_ParsesType'45'shrinks_328
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
d_ParsesParenTriple'45'shrinks_1294 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenTriple_490 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ParsesParenTriple'45'shrinks_1294 ~v0 ~v1 ~v2 v3 v4
  = du_ParsesParenTriple'45'shrinks_1294 v3 v4
du_ParsesParenTriple'45'shrinks_1294 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesParenTriple_490 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ParsesParenTriple'45'shrinks_1294 v0 v1
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
