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

module MAlonzo.Code.Once.Grammar.ExprRelRoundtrip where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ExprConvert
import qualified MAlonzo.Code.Once.Grammar.ExprPrinter
import qualified MAlonzo.Code.Once.Grammar.Printer
import qualified MAlonzo.Code.Once.Grammar.RelRoundtrip
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Parser.ExprRelation
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Grammar.ExprRelRoundtrip.Quiet
d_Quiet_6 a0 = ()
data T_Quiet_6
  = C_q'45''91''93'_8 | C_q'45'word'45'res_14 | C_q'45'TRParen_18 |
    C_q'45'TLBrace_22 | C_q'45'TRBrace_26 | C_q'45'TColon_30 |
    C_q'45'TEquals_34 | C_q'45'TArrow_38 | C_q'45'TCaret0_42 |
    C_q'45'TCaret1_46 | C_q'45'TCaretW_50 | C_q'45'TComma_54 |
    C_q'45'TSemicolon_58 | C_q'45'TAt_62 | C_q'45'TAmpersand_66 |
    C_q'45'TNewline_70 | C_q'45'TEOF_74
-- Once.Grammar.ExprRelRoundtrip.quiet→notDot
d_quiet'8594'notDot_78 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_Quiet_6 -> AgdaAny
d_quiet'8594'notDot_78 ~v0 v1 = du_quiet'8594'notDot_78 v1
du_quiet'8594'notDot_78 :: T_Quiet_6 -> AgdaAny
du_quiet'8594'notDot_78 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Grammar.ExprRelRoundtrip.quiet→notCmp
d_quiet'8594'notCmp_82 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_Quiet_6 -> AgdaAny
d_quiet'8594'notCmp_82 ~v0 v1 = du_quiet'8594'notCmp_82 v1
du_quiet'8594'notCmp_82 :: T_Quiet_6 -> AgdaAny
du_quiet'8594'notCmp_82 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Grammar.ExprRelRoundtrip.quiet→notAdd
d_quiet'8594'notAdd_86 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_Quiet_6 -> AgdaAny
d_quiet'8594'notAdd_86 ~v0 v1 = du_quiet'8594'notAdd_86 v1
du_quiet'8594'notAdd_86 :: T_Quiet_6 -> AgdaAny
du_quiet'8594'notAdd_86 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Grammar.ExprRelRoundtrip.quiet→notMul
d_quiet'8594'notMul_90 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_Quiet_6 -> AgdaAny
d_quiet'8594'notMul_90 ~v0 v1 = du_quiet'8594'notMul_90 v1
du_quiet'8594'notMul_90 :: T_Quiet_6 -> AgdaAny
du_quiet'8594'notMul_90 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Grammar.ExprRelRoundtrip.quiet→notAtom
d_quiet'8594'notAtom_94 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotAtomStart_18
d_quiet'8594'notAtom_94 ~v0 v1 = du_quiet'8594'notAtom_94 v1
du_quiet'8594'notAtom_94 ::
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotAtomStart_18
du_quiet'8594'notAtom_94 v0
  = case coe v0 of
      C_q'45''91''93'_8
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45''91''93'_20
      C_q'45'word'45'res_14
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'word'45'res_26
      C_q'45'TRParen_18
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30
      C_q'45'TLBrace_22
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TLBrace_34
      C_q'45'TRBrace_26
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRBrace_38
      C_q'45'TColon_30
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TColon_42
      C_q'45'TEquals_34
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TEquals_46
      C_q'45'TArrow_38
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TArrow_50
      C_q'45'TCaret0_42
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TCaret0_54
      C_q'45'TCaret1_46
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TCaret1_58
      C_q'45'TCaretW_50
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TCaretW_62
      C_q'45'TComma_54
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TComma_66
      C_q'45'TSemicolon_58
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TSemicolon_70
      C_q'45'TAt_62
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TAt_74
      C_q'45'TAmpersand_66
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TAmpersand_106
      C_q'45'TNewline_70
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TNewline_138
      C_q'45'TEOF_74
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TEOF_142
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprRelRoundtrip.quiet-TRParen
d_quiet'45'TRParen_100 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_Quiet_6
d_quiet'45'TRParen_100 ~v0 = du_quiet'45'TRParen_100
du_quiet'45'TRParen_100 :: T_Quiet_6
du_quiet'45'TRParen_100 = coe C_q'45'TRParen_18
-- Once.Grammar.ExprRelRoundtrip.quiet-[]
d_quiet'45''91''93'_102 :: T_Quiet_6
d_quiet'45''91''93'_102 = coe C_q'45''91''93'_8
-- Once.Grammar.ExprRelRoundtrip.quiet-in
d_quiet'45'in_106 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_Quiet_6
d_quiet'45'in_106 ~v0 = du_quiet'45'in_106
du_quiet'45'in_106 :: T_Quiet_6
du_quiet'45'in_106 = coe C_q'45'word'45'res_14
-- Once.Grammar.ExprRelRoundtrip.quiet-of
d_quiet'45'of_110 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_Quiet_6
d_quiet'45'of_110 ~v0 = du_quiet'45'of_110
du_quiet'45'of_110 :: T_Quiet_6
du_quiet'45'of_110 = coe C_q'45'word'45'res_14
-- Once.Grammar.ExprRelRoundtrip.atomExpr→app
d_atomExpr'8594'app_118 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesApp_518
d_atomExpr'8594'app_118 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'app_118 v1 v2 v3 v4
du_atomExpr'8594'app_118 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesApp_518
du_atomExpr'8594'app_118 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796 v1 v0 v3
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
         (coe du_quiet'8594'notAtom_94 (coe v2)))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→unary
d_atomExpr'8594'unary_132 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesUnary_516
d_atomExpr'8594'unary_132 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'unary_132 v1 v2 v3 v4
du_atomExpr'8594'unary_132 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesUnary_516
du_atomExpr'8594'unary_132 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
      (coe du_atomExpr'8594'app_118 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→mul
d_atomExpr'8594'mul_146 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesMul_512
d_atomExpr'8594'mul_146 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'mul_146 v1 v2 v3 v4
du_atomExpr'8594'mul_146 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesMul_512
du_atomExpr'8594'mul_146 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_720 v1 v0
      (coe
         du_atomExpr'8594'unary_132 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_726
         (coe du_quiet'8594'notMul_90 (coe v2)))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→add
d_atomExpr'8594'add_160 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAdd_508
d_atomExpr'8594'add_160 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'add_160 v1 v2 v3 v4
du_atomExpr'8594'add_160 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAdd_508
du_atomExpr'8594'add_160 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674 v1 v0
      (coe du_atomExpr'8594'mul_146 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
         (coe du_quiet'8594'notAdd_86 (coe v2)))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→cmp
d_atomExpr'8594'cmp_174 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesCmp_506
d_atomExpr'8594'cmp_174 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'cmp_174 v1 v2 v3 v4
du_atomExpr'8594'cmp_174 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesCmp_506
du_atomExpr'8594'cmp_174 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
      (coe du_atomExpr'8594'add_160 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe du_quiet'8594'notCmp_82 (coe v2))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→comp
d_atomExpr'8594'comp_188 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesComp_502
d_atomExpr'8594'comp_188 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'comp_188 v1 v2 v3 v4
du_atomExpr'8594'comp_188 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesComp_502
du_atomExpr'8594'comp_188 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562 v1 v0
      (coe du_atomExpr'8594'cmp_174 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
         (coe du_quiet'8594'notDot_78 (coe v2)))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→expr
d_atomExpr'8594'expr_202 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_500
d_atomExpr'8594'expr_202 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'expr_202 v1 v2 v3 v4
du_atomExpr'8594'expr_202 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_500
du_atomExpr'8594'expr_202 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
      (coe du_atomExpr'8594'comp_188 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→mul'
d_atomExpr'8594'mul''_216 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotAtomStart_18 ->
  AgdaAny ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesMul_512
d_atomExpr'8594'mul''_216 ~v0 v1 v2 v3 v4 v5
  = du_atomExpr'8594'mul''_216 v1 v2 v3 v4 v5
du_atomExpr'8594'mul''_216 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotAtomStart_18 ->
  AgdaAny ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesMul_512
du_atomExpr'8594'mul''_216 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_720 v1 v0
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
         (coe
            MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796 v1 v0 v4
            (coe MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802 v2)))
      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_726 v3)
-- Once.Grammar.ExprRelRoundtrip.atomExpr→add'
d_atomExpr'8594'add''_230 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotAtomStart_18 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAdd_508
d_atomExpr'8594'add''_230 ~v0 v1 v2 v3 v4 v5 v6
  = du_atomExpr'8594'add''_230 v1 v2 v3 v4 v5 v6
du_atomExpr'8594'add''_230 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotAtomStart_18 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAdd_508
du_atomExpr'8594'add''_230 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674 v1 v0
      (coe
         du_atomExpr'8594'mul''_216 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v5))
      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680 v4)
-- Once.Grammar.ExprRelRoundtrip.concreteExpr-AppArgOk
d_concreteExpr'45'AppArgOk_246 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_AppArgOk_144
d_concreteExpr'45'AppArgOk_246 ~v0 v1 ~v2
  = du_concreteExpr'45'AppArgOk_246 v1
du_concreteExpr'45'AppArgOk_246 ::
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_AppArgOk_144
du_concreteExpr'45'AppArgOk_246 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unit_80
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'int_84
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TInt_160
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'string_88
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TString_178
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'var_92
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'word_184
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'qual_98
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'word_184
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'lam_104 v3
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'app_110 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'pair_116 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'annot_122 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'binop_130 v4 v5
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unary_136 v3
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'comp_142 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'let1_150 v4 v5
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'destr_162 v6 v7 v8
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprRelRoundtrip.nqp-printGExpr
d_nqp'45'printGExpr_258 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_270 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_270
d_nqp'45'printGExpr_258 ~v0 v1 ~v2 ~v3
  = du_nqp'45'printGExpr_258 v1
du_nqp'45'printGExpr_258 ::
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_270
du_nqp'45'printGExpr_258 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unit_80
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_276
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'int_84
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TInt_406
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'string_88
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TString_424
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'var_92
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TWord_398
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'qual_98
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TWord_398
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'lam_104 v3
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_276
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'app_110 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_276
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'pair_116 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_276
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'annot_122 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_276
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'binop_130 v4 v5
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_276
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unary_136 v3
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_276
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'comp_142 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_276
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'let1_150 v4 v5
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_276
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'destr_162 v6 v7 v8
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_276
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprRelRoundtrip.rt-atom-expr
d_rt'45'atom'45'expr_266 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_270 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_522
d_rt'45'atom'45'expr_266 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unit_80
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'unit_820
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'int_84
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'int_828
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'string_88
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'str_846
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'var_92
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'var_852 v3
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'qual_98
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'qual_860
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'lam_104 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ELam_98 v7 v8
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_872
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 (coe v7)
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v8)
                          (coe v6)))
                    (coe
                       MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
                       (coe
                          MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v8)
                                (coe v6)))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
                             (coe
                                MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                (coe
                                   MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v8)
                                      (coe v6)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_720
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 (coe v7)
                                      (coe
                                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                         (coe v8) (coe v6)))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
                                      (coe
                                         MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                            (coe v2))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                               (coe v8) (coe v6)))
                                         (coe
                                            MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'lambda_880
                                            (coe
                                               MAlonzo.Code.Once.Parser.ExprRelation.C_plp'45'arg_922
                                               (coe
                                                  MAlonzo.Code.Once.Parser.ExprRelation.C_plp'45'body_912
                                                  (d_rt'45'expr_274
                                                     (coe v8) (coe v6)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                        (coe v2))
                                                     (coe du_quiet'45'TRParen_100)
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280)))))
                                         (coe
                                            MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
                                            (coe
                                               MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_726
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1126)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'app_110 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EApp_100 v8 v9
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_872
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v8)
                          (coe v6))
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v9)
                          (coe v7)))
                    (d_rt'45'expr'45'app'45'body_286
                       (coe v8) (coe v9) (coe v6) (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                       (coe du_quiet'45'TRParen_100)
                       (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1126)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'pair_116 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EPair_102 v8 v9
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_872
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TComma_38)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v9))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))))
                    (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                       (coe v8) (coe v6))
                    (d_rt'45'expr_274
                       (coe v8) (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TComma_38)
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v9))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))))
                       (coe C_q'45'TComma_54)
                       (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TComma_320))
                    (coe
                       MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'pair_1138
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                       (d_rt'45'expr_274
                          (coe v9) (coe v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                          (coe du_quiet'45'TRParen_100)
                          (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))
                       (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppt'45'close_1156))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'annot_122 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EAnnot_114 v8 v9
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_872
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TColon_24)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v9))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))))
                    (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                       (coe v8) (coe v6))
                    (d_rt'45'expr_274
                       (coe v8) (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TColon_24)
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v9))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))))
                       (coe C_q'45'TColon_30)
                       (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TColon_292))
                    (coe
                       MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'annot_1148
                       (coe
                          MAlonzo.Code.Once.Grammar.RelRoundtrip.du_rt'45'type_86 (coe v9)
                          (coe v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'binop_130 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EBinOp_108 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_872
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gBinOpToRaw_6 (coe v9))
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v10)
                          (coe v7))
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v11)
                          (coe v8)))
                    (d_rt'45'expr'45'binop'45'body_300
                       (coe v10) (coe v11) (coe v9) (coe v7) (coe v8) (coe v2))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1126)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unary_136 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EUnaryOp_110 v8
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_872
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64
                       (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                          (coe v8) (coe v6)))
                    (coe
                       MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
                       (coe
                          MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64
                             (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                (coe v8) (coe v6)))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
                             (coe
                                MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                (coe
                                   MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64
                                   (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                      (coe v8) (coe v6)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_720
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64
                                      (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                         (coe v8) (coe v6)))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'neg_776
                                      (coe
                                         du_atomExpr'8594'unary_132
                                         (coe
                                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                            (coe v8) (coe v6))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                            (coe v2))
                                         (coe du_quiet'45'TRParen_100)
                                         (coe
                                            d_rt'45'atom'45'expr_266 (coe v8) (coe v6)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                               (coe v2))
                                            (coe
                                               MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_726
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1126)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'comp_142 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ECompose_112 v8 v9
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_872
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                          (coe
                             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36
                             (coe ("compose" :: Data.Text.Text)))
                          (coe
                             MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v8)
                             (coe v6)))
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v9)
                          (coe v7)))
                    (d_rt'45'expr'45'compose'45'body_312
                       (coe v8) (coe v9) (coe v6) (coe v7) (coe v2))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1126)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'let1_150 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ELet_104 v9 v10
               -> case coe v9 of
                    (:) v11 v12
                      -> case coe v11 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_872
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                        (coe v14) (coe v7))
                                     (coe
                                        MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                        (coe v10) (coe v8)))
                                  (coe
                                     MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                           (coe v2))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                              (coe v14) (coe v7))
                                           (coe
                                              MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                              (coe v10) (coe v8)))
                                        (coe
                                           MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
                                           (coe
                                              MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                 (coe v2))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 (coe v13)
                                                 (coe
                                                    MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                                    (coe v14) (coe v7))
                                                 (coe
                                                    MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                                    (coe v10) (coe v8)))
                                              (coe
                                                 MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_720
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                    (coe v2))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Syntax.C_RLet_46
                                                    (coe v13)
                                                    (coe
                                                       MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                                       (coe v14) (coe v7))
                                                    (coe
                                                       MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                                       (coe v10) (coe v8)))
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                          (coe v2))
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Syntax.C_RLet_46
                                                          (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                                             (coe v14) (coe v7))
                                                          (coe
                                                             MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                                             (coe v10) (coe v8)))
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'let_888
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.ExprRelation.C_plet'45'single_936
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                                   (coe ("in" :: Data.Text.Text)))
                                                                (coe
                                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                   (coe
                                                                      MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                                                      (coe v10))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                      (coe v2))))
                                                             (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                                                (coe v14) (coe v7))
                                                             (d_rt'45'expr_274
                                                                (coe v14) (coe v7)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                                      (coe
                                                                         ("in" :: Data.Text.Text)))
                                                                   (coe
                                                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                      (coe
                                                                         MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                                                         (coe v10))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                         (coe
                                                                            MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                         (coe v2))))
                                                                (coe C_q'45'word'45'res_14)
                                                                (coe
                                                                   MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TWord_398))
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.ExprRelation.C_plin_948
                                                                (d_rt'45'expr_274
                                                                   (coe v10) (coe v8)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                      (coe v2))
                                                                   (coe du_quiet'45'TRParen_100)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280)))))
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_726
                                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                              (coe
                                                 MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                        (coe
                                           MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1126)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'destr_162 v9 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EDestruct_106 v12 v13 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_872
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v12)
                          (coe v9))
                       (coe v13)
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v14)
                          (coe v10))
                       (coe v15)
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v16)
                          (coe v11)))
                    (coe
                       MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
                       (coe
                          MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50
                             (coe
                                MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v12)
                                (coe v9))
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v14)
                                (coe v10))
                             (coe v15)
                             (coe
                                MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v16)
                                (coe v11)))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
                             (coe
                                MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                (coe
                                   MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50
                                   (coe
                                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                      (coe v12) (coe v9))
                                   (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                      (coe v14) (coe v10))
                                   (coe v15)
                                   (coe
                                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                      (coe v16) (coe v11)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_720
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50
                                      (coe
                                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                         (coe v12) (coe v9))
                                      (coe v13)
                                      (coe
                                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                         (coe v14) (coe v10))
                                      (coe v15)
                                      (coe
                                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                         (coe v16) (coe v11)))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
                                      (coe
                                         MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                            (coe v2))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50
                                            (coe
                                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                               (coe v12) (coe v9))
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                               (coe v14) (coe v10))
                                            (coe v15)
                                            (coe
                                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                               (coe v16) (coe v11)))
                                         (coe
                                            MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'destruct_896
                                            (coe
                                               MAlonzo.Code.Once.Parser.ExprRelation.C_pd'45'mk_960
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                     (coe ("of" :: Data.Text.Text)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Token.C_TLBrace_20)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                           (coe ("Left" :: Data.Text.Text)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                              (coe v13))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                                                    (coe v14))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                                          (coe
                                                                             ("Right"
                                                                              ::
                                                                              Data.Text.Text)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                                             (coe v15))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                                                                             (coe
                                                                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                                                                   (coe v16))
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Parser.Token.C_TRBrace_22)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                      (coe
                                                                                         v2))))))))))))))
                                               (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                                  (coe v12) (coe v9))
                                               (d_rt'45'expr_274
                                                  (coe v12) (coe v9)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                        (coe ("of" :: Data.Text.Text)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Token.C_TLBrace_20)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                              (coe ("Left" :: Data.Text.Text)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                                 (coe v13))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                                                                 (coe
                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                    (coe
                                                                       MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                                                       (coe v14))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                                             (coe
                                                                                ("Right"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                                                (coe v15))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                                                                                (coe
                                                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                                                                      (coe v16))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Parser.Token.C_TRBrace_22)
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                                         (coe
                                                                                            v2))))))))))))))
                                                  (coe C_q'45'word'45'res_14)
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TWord_398))
                                               (coe
                                                  MAlonzo.Code.Once.Parser.ExprRelation.C_pdof_970
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.ExprRelation.C_pdb_986
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                              (coe ("Right" :: Data.Text.Text)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                                 (coe v15))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                                                                 (coe
                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                    (coe
                                                                       MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                                                       (coe v16))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Token.C_TRBrace_22)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                          (coe v2))))))))
                                                     (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                                        (coe v14) (coe v10))
                                                     (d_rt'45'expr_274
                                                        (coe v14) (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                                 (coe ("Right" :: Data.Text.Text)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                                                    (coe v15))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                       (coe
                                                                          MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                                                          (coe v16))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Token.C_TRBrace_22)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                             (coe v2))))))))
                                                        (coe C_q'45'TSemicolon_58)
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TSemicolon_324))
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.ExprRelation.C_prb_1002
                                                        (d_rt'45'expr_274
                                                           (coe v16) (coe v11)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.Parser.Token.C_TRBrace_22)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                 (coe v2)))
                                                           (coe C_q'45'TRBrace_26)
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRBrace_288)))))))
                                         (coe
                                            MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
                                            (coe
                                               MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_726
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1126)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprRelRoundtrip.rt-expr
d_rt'45'expr_274 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_270 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_500
d_rt'45'expr_274 v0 v1 v2 v3 v4
  = coe
      du_atomExpr'8594'expr_202
      (coe
         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
         (coe v1))
      (coe v2) (coe v3)
      (coe d_rt'45'atom'45'expr_266 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Grammar.ExprRelRoundtrip.rt-expr-app-body
d_rt'45'expr'45'app'45'body_286 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_270 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_500
d_rt'45'expr'45'app'45'body_286 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562 v4
         (coe
            MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
            (coe
               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
               (coe v2))
            (coe
               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
               (coe v3)))
         (coe
            MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
            (coe
               MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674 v4
               (coe
                  MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                  (coe
                     MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                     (coe v2))
                  (coe
                     MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                     (coe v3)))
               (coe
                  MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_720 v4
                  (coe
                     MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                     (coe
                        MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                        (coe v2))
                     (coe
                        MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
                     (coe
                        MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                           (coe v4))
                        (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                           (coe v0) (coe v2))
                        (d_rt'45'atom'45'expr_266
                           (coe v0) (coe v2)
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                              (coe v4))
                           (coe du_nqp'45'printGExpr_258 (coe v3)))
                        (coe
                           MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'arg_816 v4
                           (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                              (coe v1) (coe v3))
                           (coe du_concreteExpr'45'AppArgOk_246 (coe v3))
                           (d_rt'45'atom'45'expr_266 (coe v1) (coe v3) (coe v4) (coe v6))
                           (coe
                              MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
                              (coe du_quiet'8594'notAtom_94 (coe v5))))))
                  (coe
                     MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_726
                     (coe du_quiet'8594'notMul_90 (coe v5))))
               (coe
                  MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
                  (coe du_quiet'8594'notAdd_86 (coe v5))))
            (coe du_quiet'8594'notCmp_82 (coe v5)))
         (coe
            MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
            (coe du_quiet'8594'notDot_78 (coe v5))))
-- Once.Grammar.ExprRelRoundtrip.rt-expr-binop-body
d_rt'45'expr'45'binop'45'body_300 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.T_BinOp_58 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_500
d_rt'45'expr'45'binop'45'body_300 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Grammar.C_OpAdd_60
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
                   (coe
                      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                      (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                         (coe v0) (coe v3))
                      (coe
                         du_atomExpr'8594'mul''_216
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TPlus_86)
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                         (coe
                            d_rt'45'atom'45'expr_266 (coe v0) (coe v3)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48)
                               (coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                            (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TPlus_336)))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'plus_694
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                            (coe v1) (coe v4))
                         (coe
                            du_atomExpr'8594'mul''_216
                            (coe
                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                               (coe v4))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                            (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30)
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               d_rt'45'atom'45'expr_266 (coe v1) (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                               (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280)))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpSub_62
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
                   (coe
                      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TMinus_50)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                      (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                         (coe v0) (coe v3))
                      (coe
                         du_atomExpr'8594'mul''_216
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TMinus_50)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TMinus_90)
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                         (coe
                            d_rt'45'atom'45'expr_266 (coe v0) (coe v3)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TMinus_50)
                               (coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                            (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TMinus_340)))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'minus_708
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                            (coe v1) (coe v4))
                         (coe
                            du_atomExpr'8594'mul''_216
                            (coe
                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                               (coe v4))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                            (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30)
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               d_rt'45'atom'45'expr_266 (coe v1) (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                               (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280)))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpMul_64
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
                   (coe
                      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                         (coe MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12)
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                            (coe v3))
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                            (coe v4)))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_720
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TStar_52)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                            (coe v0) (coe v3))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TStar_52)
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe
                                        MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                        (coe v1))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                        (coe v5))))
                               (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                  (coe v0) (coe v3))
                               (d_rt'45'atom'45'expr_266
                                  (coe v0) (coe v3)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TStar_52)
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                           (coe v1))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                           (coe v5))))
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TStar_344))
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TStar_94))))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'star_740
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                            (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                               (coe v1) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                  (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                     (coe v1) (coe v4))
                                  (d_rt'45'atom'45'expr_266
                                     (coe v1) (coe v4)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))
                                  (coe
                                     MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_726
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpDiv_66
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
                   (coe
                      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                         (coe MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14)
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                            (coe v3))
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                            (coe v4)))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_720
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TSlash_54)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                            (coe v0) (coe v3))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TSlash_54)
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe
                                        MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                        (coe v1))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                        (coe v5))))
                               (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                  (coe v0) (coe v3))
                               (d_rt'45'atom'45'expr_266
                                  (coe v0) (coe v3)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TSlash_54)
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                           (coe v1))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                           (coe v5))))
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TSlash_348))
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TSlash_98))))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'slash_754
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                            (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                               (coe v1) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                  (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                     (coe v1) (coe v4))
                                  (d_rt'45'atom'45'expr_266
                                     (coe v1) (coe v4)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))
                                  (coe
                                     MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_726
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpMod_68
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpMod_16)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
                   (coe
                      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_674
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                         (coe MAlonzo.Code.Once.Lang.Syntax.C_OpMod_16)
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                            (coe v3))
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                            (coe v4)))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_720
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TPercent_56)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                            (coe v0) (coe v3))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TPercent_56)
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe
                                        MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                        (coe v1))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                        (coe v5))))
                               (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                  (coe v0) (coe v3))
                               (d_rt'45'atom'45'expr_266
                                  (coe v0) (coe v3)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TPercent_56)
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8
                                           (coe v1))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                           (coe v5))))
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TPercent_352))
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
                                  (coe
                                     MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TPercent_102))))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'percent_768
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                            (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                               (coe v1) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_784
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_796
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                  (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                                     (coe v1) (coe v4))
                                  (d_rt'45'atom'45'expr_266
                                     (coe v1) (coe v4)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))
                                  (coe
                                     MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_802
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_726
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_680
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpLt_70
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpLt_18)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'lt_602
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TLt_60)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TLt_110)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v0) (coe v3)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TLt_60)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLt_360)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                         (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v1) (coe v4)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpLe_72
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpLe_20)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'le_614
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TLe_62)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TLe_114)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v0) (coe v3)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TLe_62)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLe_364)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                         (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v1) (coe v4)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpGt_74
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpGt_22)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'gt_626
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TGt_64)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TGt_118)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v0) (coe v3)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TGt_64)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TGt_368)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                         (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v1) (coe v4)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpGe_76
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpGe_24)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'ge_638
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TGe_66)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TGe_122)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v0) (coe v3)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TGe_66)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TGe_372)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                         (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v1) (coe v4)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpEq_78
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpEq_26)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'eq_650
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TEqEq_68)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TEqEq_126)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v0) (coe v3)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TEqEq_68)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TEqEq_376)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                         (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v1) (coe v4)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpNe_80
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62
                   (coe MAlonzo.Code.Once.Lang.Syntax.C_OpNe_28)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'ne_662
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TNeq_70)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TNeq_130)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v0) (coe v3)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TNeq_70)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TNeq_380)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                         (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         d_rt'45'atom'45'expr_266 (coe v1) (coe v4)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprRelRoundtrip.rt-expr-compose-body
d_rt'45'expr'45'compose'45'body_312 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_500
d_rt'45'expr'45'compose'45'body_312 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_550
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_562
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.Parser.Token.C_TDot_46)
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v4))))
         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
            (coe v0) (coe v2))
         (coe
            MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
            (coe
               du_atomExpr'8594'add''_230
               (coe
                  MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v0)
                  (coe v2))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.Parser.Token.C_TDot_46)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v4))))
               (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TDot_82)
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe
                  d_rt'45'atom'45'expr_266 (coe v0) (coe v2)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.Parser.Token.C_TDot_46)
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v4))))
                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TDot_332)))
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe
            MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'dot_582
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v4))
            (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
               (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_590
               (coe
                  du_atomExpr'8594'add''_230
                  (coe
                     MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12 (coe v1)
                     (coe v3))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v4))
                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe
                     d_rt'45'atom'45'expr_266 (coe v1) (coe v3)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v4))
                     (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_280)))
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
            (coe
               MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_568
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
-- Once.Grammar.ExprRelRoundtrip.round-trip-rel-expr
d_round'45'trip'45'rel'45'expr_606 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_86 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_500
d_round'45'trip'45'rel'45'expr_606 v0 v1
  = coe
      d_rt'45'expr_274 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe C_q'45''91''93'_8)
      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45''91''93'_272)
