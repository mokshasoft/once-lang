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
import qualified MAlonzo.Code.Once.Internal.Syntax
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
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesApp_512
d_atomExpr'8594'app_118 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'app_118 v1 v2 v3 v4
du_atomExpr'8594'app_118 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesApp_512
du_atomExpr'8594'app_118 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790 v1 v0 v3
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
         (coe du_quiet'8594'notAtom_94 (coe v2)))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→unary
d_atomExpr'8594'unary_132 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesUnary_510
d_atomExpr'8594'unary_132 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'unary_132 v1 v2 v3 v4
du_atomExpr'8594'unary_132 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesUnary_510
du_atomExpr'8594'unary_132 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
      (coe du_atomExpr'8594'app_118 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→mul
d_atomExpr'8594'mul_146 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesMul_506
d_atomExpr'8594'mul_146 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'mul_146 v1 v2 v3 v4
du_atomExpr'8594'mul_146 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesMul_506
du_atomExpr'8594'mul_146 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_714 v1 v0
      (coe
         du_atomExpr'8594'unary_132 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_720
         (coe du_quiet'8594'notMul_90 (coe v2)))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→add
d_atomExpr'8594'add_160 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAdd_502
d_atomExpr'8594'add_160 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'add_160 v1 v2 v3 v4
du_atomExpr'8594'add_160 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAdd_502
du_atomExpr'8594'add_160 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668 v1 v0
      (coe du_atomExpr'8594'mul_146 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
         (coe du_quiet'8594'notAdd_86 (coe v2)))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→cmp
d_atomExpr'8594'cmp_174 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesCmp_500
d_atomExpr'8594'cmp_174 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'cmp_174 v1 v2 v3 v4
du_atomExpr'8594'cmp_174 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesCmp_500
du_atomExpr'8594'cmp_174 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
      (coe du_atomExpr'8594'add_160 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe du_quiet'8594'notCmp_82 (coe v2))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→comp
d_atomExpr'8594'comp_188 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesComp_496
d_atomExpr'8594'comp_188 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'comp_188 v1 v2 v3 v4
du_atomExpr'8594'comp_188 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesComp_496
du_atomExpr'8594'comp_188 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556 v1 v0
      (coe du_atomExpr'8594'cmp_174 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
         (coe du_quiet'8594'notDot_78 (coe v2)))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→expr
d_atomExpr'8594'expr_202 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_494
d_atomExpr'8594'expr_202 ~v0 v1 v2 v3 v4
  = du_atomExpr'8594'expr_202 v1 v2 v3 v4
du_atomExpr'8594'expr_202 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_494
du_atomExpr'8594'expr_202 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
      (coe du_atomExpr'8594'comp_188 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Grammar.ExprRelRoundtrip.atomExpr→mul'
d_atomExpr'8594'mul''_216 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotAtomStart_18 ->
  AgdaAny ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesMul_506
d_atomExpr'8594'mul''_216 ~v0 v1 v2 v3 v4 v5
  = du_atomExpr'8594'mul''_216 v1 v2 v3 v4 v5
du_atomExpr'8594'mul''_216 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotAtomStart_18 ->
  AgdaAny ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesMul_506
du_atomExpr'8594'mul''_216 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_714 v1 v0
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
         (coe
            MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790 v1 v0 v4
            (coe MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796 v2)))
      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_720 v3)
-- Once.Grammar.ExprRelRoundtrip.atomExpr→add'
d_atomExpr'8594'add''_230 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotAtomStart_18 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAdd_502
d_atomExpr'8594'add''_230 ~v0 v1 v2 v3 v4 v5 v6
  = du_atomExpr'8594'add''_230 v1 v2 v3 v4 v5 v6
du_atomExpr'8594'add''_230 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotAtomStart_18 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAdd_502
du_atomExpr'8594'add''_230 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668 v1 v0
      (coe
         du_atomExpr'8594'mul''_216 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v5))
      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674 v4)
-- Once.Grammar.ExprRelRoundtrip.concreteExpr-AppArgOk
d_concreteExpr'45'AppArgOk_246 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_AppArgOk_144
d_concreteExpr'45'AppArgOk_246 ~v0 v1 ~v2
  = du_concreteExpr'45'AppArgOk_246 v1
du_concreteExpr'45'AppArgOk_246 ::
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_AppArgOk_144
du_concreteExpr'45'AppArgOk_246 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unit_78
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'int_82
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TInt_160
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'var_86
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'word_178
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'qual_92
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'word_178
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'lam_98 v3
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'app_104 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'pair_110 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'annot_116 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'binop_124 v4 v5
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unary_130 v3
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'comp_136 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'let1_144 v4 v5
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'destr_156 v6 v7 v8
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_aao'45'TLParen_148
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprRelRoundtrip.nqp-printGExpr
d_nqp'45'printGExpr_258 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_264 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_264
d_nqp'45'printGExpr_258 ~v0 v1 ~v2 ~v3
  = du_nqp'45'printGExpr_258 v1
du_nqp'45'printGExpr_258 ::
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_264
du_nqp'45'printGExpr_258 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unit_78
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_270
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'int_82
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TInt_400
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'var_86
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TWord_392
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'qual_92
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TWord_392
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'lam_98 v3
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_270
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'app_104 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_270
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'pair_110 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_270
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'annot_116 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_270
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'binop_124 v4 v5
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_270
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unary_130 v3
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_270
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'comp_136 v3 v4
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_270
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'let1_144 v4 v5
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_270
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'destr_156 v6 v7 v8
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLParen_270
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprRelRoundtrip.rt-atom-expr
d_rt'45'atom'45'expr_266 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_264 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesAtomExpr_516
d_rt'45'atom'45'expr_266 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unit_78
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'unit_814
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'int_82
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'int_822
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'var_86
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'var_840 v3
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'qual_92
        -> coe MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'qual_848
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'lam_98 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ELam_90 v7 v8
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_860
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Internal.Syntax.C_RLam_40 (coe v7)
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v8)
                          (coe v6)))
                    (coe
                       MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
                       (coe
                          MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Internal.Syntax.C_RLam_40 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v8)
                                (coe v6)))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
                             (coe
                                MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                (coe
                                   MAlonzo.Code.Once.Internal.Syntax.C_RLam_40 (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v8)
                                      (coe v6)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_714
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                   (coe
                                      MAlonzo.Code.Once.Internal.Syntax.C_RLam_40 (coe v7)
                                      (coe
                                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                         (coe v8) (coe v6)))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
                                      (coe
                                         MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                            (coe v2))
                                         (coe
                                            MAlonzo.Code.Once.Internal.Syntax.C_RLam_40 (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                               (coe v8) (coe v6)))
                                         (coe
                                            MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'lambda_868
                                            (coe
                                               MAlonzo.Code.Once.Parser.ExprRelation.C_plp'45'arg_910
                                               (coe
                                                  MAlonzo.Code.Once.Parser.ExprRelation.C_plp'45'body_900
                                                  (d_rt'45'expr_274
                                                     (coe v8) (coe v6)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                        (coe v2))
                                                     (coe du_quiet'45'TRParen_100)
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274)))))
                                         (coe
                                            MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
                                            (coe
                                               MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_720
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1114)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'app_104 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EApp_92 v8 v9
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_860
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Internal.Syntax.C_RApp_38
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v8)
                          (coe v6))
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v9)
                          (coe v7)))
                    (d_rt'45'expr'45'app'45'body_286
                       (coe v8) (coe v9) (coe v6) (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                       (coe du_quiet'45'TRParen_100)
                       (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1114)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'pair_110 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EPair_94 v8 v9
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_860
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TComma_38)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v9))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))))
                    (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
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
                       (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TComma_314))
                    (coe
                       MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'pair_1126
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                       (d_rt'45'expr_274
                          (coe v9) (coe v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                          (coe du_quiet'45'TRParen_100)
                          (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))
                       (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppt'45'close_1144))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'annot_116 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EAnnot_106 v8 v9
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_860
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TColon_24)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v9))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))))
                    (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
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
                       (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TColon_286))
                    (coe
                       MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'annot_1136
                       (coe
                          MAlonzo.Code.Once.Grammar.RelRoundtrip.du_rt'45'type_86 (coe v9)
                          (coe v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'binop_124 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EBinOp_100 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_860
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gBinOpToRaw_6 (coe v9))
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v10)
                          (coe v7))
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v11)
                          (coe v8)))
                    (d_rt'45'expr'45'binop'45'body_300
                       (coe v10) (coe v11) (coe v9) (coe v7) (coe v8) (coe v2))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1114)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unary_130 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EUnaryOp_102 v8
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_860
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Internal.Syntax.C_RNeg_58
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v8)
                          (coe v6)))
                    (coe
                       MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
                       (coe
                          MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Internal.Syntax.C_RNeg_58
                             (coe
                                MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v8)
                                (coe v6)))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
                             (coe
                                MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                (coe
                                   MAlonzo.Code.Once.Internal.Syntax.C_RNeg_58
                                   (coe
                                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v8)
                                      (coe v6)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_714
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                   (coe
                                      MAlonzo.Code.Once.Internal.Syntax.C_RNeg_58
                                      (coe
                                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                         (coe v8) (coe v6)))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'neg_770
                                      (coe
                                         du_atomExpr'8594'unary_132
                                         (coe
                                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
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
                                               MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_720
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1114)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'comp_136 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ECompose_104 v8 v9
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_860
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Internal.Syntax.C_RApp_38
                       (coe
                          MAlonzo.Code.Once.Internal.Syntax.C_RApp_38
                          (coe
                             MAlonzo.Code.Once.Internal.Syntax.C_RVar_32
                             (coe ("compose" :: Data.Text.Text)))
                          (coe
                             MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v8)
                             (coe v6)))
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v9)
                          (coe v7)))
                    (d_rt'45'expr'45'compose'45'body_312
                       (coe v8) (coe v9) (coe v6) (coe v7) (coe v2))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1114)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'let1_144 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ELet_96 v9 v10
               -> case coe v9 of
                    (:) v11 v12
                      -> case coe v11 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_860
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                  (coe
                                     MAlonzo.Code.Once.Internal.Syntax.C_RLet_42 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                        (coe v14) (coe v7))
                                     (coe
                                        MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                        (coe v10) (coe v8)))
                                  (coe
                                     MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                           (coe v2))
                                        (coe
                                           MAlonzo.Code.Once.Internal.Syntax.C_RLet_42 (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                              (coe v14) (coe v7))
                                           (coe
                                              MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                              (coe v10) (coe v8)))
                                        (coe
                                           MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
                                           (coe
                                              MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                 (coe v2))
                                              (coe
                                                 MAlonzo.Code.Once.Internal.Syntax.C_RLet_42
                                                 (coe v13)
                                                 (coe
                                                    MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                                    (coe v14) (coe v7))
                                                 (coe
                                                    MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                                    (coe v10) (coe v8)))
                                              (coe
                                                 MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_714
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                    (coe v2))
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Syntax.C_RLet_42
                                                    (coe v13)
                                                    (coe
                                                       MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                                       (coe v14) (coe v7))
                                                    (coe
                                                       MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                                       (coe v10) (coe v8)))
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                          (coe v2))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Syntax.C_RLet_42
                                                          (coe v13)
                                                          (coe
                                                             MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                                             (coe v14) (coe v7))
                                                          (coe
                                                             MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                                             (coe v10) (coe v8)))
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'let_876
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.ExprRelation.C_plet'45'single_924
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
                                                             (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
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
                                                                   MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TWord_392))
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.ExprRelation.C_plin_936
                                                                (d_rt'45'expr_274
                                                                   (coe v10) (coe v8)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                                      (coe v2))
                                                                   (coe du_quiet'45'TRParen_100)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274)))))
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_720
                                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                              (coe
                                                 MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                        (coe
                                           MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1114)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'destr_156 v9 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EDestruct_98 v12 v13 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'paren_860
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                    (coe
                       MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_46
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v12)
                          (coe v9))
                       (coe v13)
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v14)
                          (coe v10))
                       (coe v15)
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v16)
                          (coe v11)))
                    (coe
                       MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
                       (coe
                          MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_46
                             (coe
                                MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v12)
                                (coe v9))
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v14)
                                (coe v10))
                             (coe v15)
                             (coe
                                MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v16)
                                (coe v11)))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
                             (coe
                                MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                (coe
                                   MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_46
                                   (coe
                                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                      (coe v12) (coe v9))
                                   (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                      (coe v14) (coe v10))
                                   (coe v15)
                                   (coe
                                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                      (coe v16) (coe v11)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_714
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v2))
                                   (coe
                                      MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_46
                                      (coe
                                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                         (coe v12) (coe v9))
                                      (coe v13)
                                      (coe
                                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                         (coe v14) (coe v10))
                                      (coe v15)
                                      (coe
                                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                         (coe v16) (coe v11)))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
                                      (coe
                                         MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                            (coe v2))
                                         (coe
                                            MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_46
                                            (coe
                                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                               (coe v12) (coe v9))
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                               (coe v14) (coe v10))
                                            (coe v15)
                                            (coe
                                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                               (coe v16) (coe v11)))
                                         (coe
                                            MAlonzo.Code.Once.Parser.ExprRelation.C_pae'45'destruct_884
                                            (coe
                                               MAlonzo.Code.Once.Parser.ExprRelation.C_pd'45'mk_948
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
                                               (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
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
                                                     MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TWord_392))
                                               (coe
                                                  MAlonzo.Code.Once.Parser.ExprRelation.C_pdof_958
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.ExprRelation.C_pdb_974
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
                                                     (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
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
                                                           MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TSemicolon_318))
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.ExprRelation.C_prb_990
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
                                                              MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRBrace_282)))))))
                                         (coe
                                            MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
                                            (coe
                                               MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                                   (coe
                                      MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_720
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                (coe
                                   MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe
                             MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                    (coe MAlonzo.Code.Once.Parser.ExprRelation.C_ppc'45'close_1114)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprRelRoundtrip.rt-expr
d_rt'45'expr_274 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_264 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_494
d_rt'45'expr_274 v0 v1 v2 v3 v4
  = coe
      du_atomExpr'8594'expr_202
      (coe
         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
         (coe v1))
      (coe v2) (coe v3)
      (coe d_rt'45'atom'45'expr_266 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Grammar.ExprRelRoundtrip.rt-expr-app-body
d_rt'45'expr'45'app'45'body_286 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_Quiet_6 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_NotQualPrefix_264 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_494
d_rt'45'expr'45'app'45'body_286 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556 v4
         (coe
            MAlonzo.Code.Once.Internal.Syntax.C_RApp_38
            (coe
               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
               (coe v2))
            (coe
               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
               (coe v3)))
         (coe
            MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
            (coe
               MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668 v4
               (coe
                  MAlonzo.Code.Once.Internal.Syntax.C_RApp_38
                  (coe
                     MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                     (coe v2))
                  (coe
                     MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                     (coe v3)))
               (coe
                  MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_714 v4
                  (coe
                     MAlonzo.Code.Once.Internal.Syntax.C_RApp_38
                     (coe
                        MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                        (coe v2))
                     (coe
                        MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
                     (coe
                        MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                           (coe v4))
                        (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                           (coe v0) (coe v2))
                        (d_rt'45'atom'45'expr_266
                           (coe v0) (coe v2)
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                              (coe v4))
                           (coe du_nqp'45'printGExpr_258 (coe v3)))
                        (coe
                           MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'arg_810 v4
                           (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                              (coe v1) (coe v3))
                           (coe du_concreteExpr'45'AppArgOk_246 (coe v3))
                           (d_rt'45'atom'45'expr_266 (coe v1) (coe v3) (coe v4) (coe v6))
                           (coe
                              MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
                              (coe du_quiet'8594'notAtom_94 (coe v5))))))
                  (coe
                     MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_720
                     (coe du_quiet'8594'notMul_90 (coe v5))))
               (coe
                  MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
                  (coe du_quiet'8594'notAdd_86 (coe v5))))
            (coe du_quiet'8594'notCmp_82 (coe v5)))
         (coe
            MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
            (coe du_quiet'8594'notDot_78 (coe v5))))
-- Once.Grammar.ExprRelRoundtrip.rt-expr-binop-body
d_rt'45'expr'45'binop'45'body_300 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.T_BinOp_52 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_494
d_rt'45'expr'45'binop'45'body_300 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Grammar.C_OpAdd_54
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpAdd_8)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
                   (coe
                      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                      (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                         (coe v0) (coe v3))
                      (coe
                         du_atomExpr'8594'mul''_216
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
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
                            (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TPlus_330)))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'plus_688
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                            (coe v1) (coe v4))
                         (coe
                            du_atomExpr'8594'mul''_216
                            (coe
                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
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
                               (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274)))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpSub_56
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpSub_10)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
                   (coe
                      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TMinus_50)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                      (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                         (coe v0) (coe v3))
                      (coe
                         du_atomExpr'8594'mul''_216
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
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
                            (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TMinus_334)))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'minus_702
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                            (coe v1) (coe v4))
                         (coe
                            du_atomExpr'8594'mul''_216
                            (coe
                               MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
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
                               (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274)))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpMul_58
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpMul_12)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
                   (coe
                      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe
                         MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                         (coe MAlonzo.Code.Once.Internal.Syntax.C_OpMul_12)
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                            (coe v3))
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                            (coe v4)))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_714
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TStar_52)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                            (coe v0) (coe v3))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790
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
                               (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
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
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TStar_338))
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TStar_94))))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'star_734
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                            (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                               (coe v1) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                  (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                     (coe v1) (coe v4))
                                  (d_rt'45'atom'45'expr_266
                                     (coe v1) (coe v4)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))
                                  (coe
                                     MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_720
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpDiv_60
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpDiv_14)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
                   (coe
                      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe
                         MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                         (coe MAlonzo.Code.Once.Internal.Syntax.C_OpDiv_14)
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                            (coe v3))
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                            (coe v4)))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_714
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TSlash_54)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                            (coe v0) (coe v3))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790
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
                               (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
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
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TSlash_342))
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TSlash_98))))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'slash_748
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                            (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                               (coe v1) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                  (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                     (coe v1) (coe v4))
                                  (d_rt'45'atom'45'expr_266
                                     (coe v1) (coe v4)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))
                                  (coe
                                     MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_720
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpMod_62
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpMod_16)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
                   (coe
                      MAlonzo.Code.Once.Parser.ExprRelation.C_pa'45'mk_668
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                      (coe
                         MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                         (coe MAlonzo.Code.Once.Internal.Syntax.C_OpMod_16)
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                            (coe v3))
                         (coe
                            MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                            (coe v4)))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pm'45'mk_714
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TPercent_56)
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))))
                         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                            (coe v0) (coe v3))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790
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
                               (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
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
                                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TPercent_346))
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
                                  (coe
                                     MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TPercent_102))))
                         (coe
                            MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'percent_762
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                            (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                               (coe v1) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pu'45'app_778
                               (coe
                                  MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'mk_790
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                  (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
                                     (coe v1) (coe v4))
                                  (d_rt'45'atom'45'expr_266
                                     (coe v1) (coe v4)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))
                                  (coe
                                     MAlonzo.Code.Once.Parser.ExprRelation.C_papp'45'done_796
                                     (coe
                                        MAlonzo.Code.Once.Parser.ExprRelation.C_nas'45'TRParen_30))))
                            (coe
                               MAlonzo.Code.Once.Parser.ExprRelation.C_pmt'45'done_720
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                      (coe
                         MAlonzo.Code.Once.Parser.ExprRelation.C_pat'45'done_674
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpLt_64
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpLt_18)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'lt_596
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLt_354)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpLe_66
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpLe_20)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'le_608
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TLe_358)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpGt_68
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpGt_22)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'gt_620
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TGt_362)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpGe_70
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpGe_24)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'ge_632
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TGe_366)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpEq_72
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpEq_26)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'eq_644
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TEqEq_370)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Grammar.C_OpNe_74
        -> coe
             MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
             (coe
                MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56
                   (coe MAlonzo.Code.Once.Internal.Syntax.C_OpNe_28)
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
                      (coe v4)))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'ne_656
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v5)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TNeq_374)))
                   (coe
                      du_atomExpr'8594'add''_230
                      (coe
                         MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
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
                         (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274))))
                (coe
                   MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprRelRoundtrip.rt-expr-compose-body
d_rt'45'expr'45'compose'45'body_312 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_494
d_rt'45'expr'45'compose'45'body_312 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Parser.ExprRelation.C_pe'45'mk_544
      (coe
         MAlonzo.Code.Once.Parser.ExprRelation.C_pc'45'mk_556
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe MAlonzo.Code.Once.Parser.Token.C_TDot_46)
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe MAlonzo.Code.Once.Grammar.ExprPrinter.d_printGExpr_8 (coe v1))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v4))))
         (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
            (coe v0) (coe v2))
         (coe
            MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
            (coe
               du_atomExpr'8594'add''_230
               (coe
                  MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v0)
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
                  (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TDot_326)))
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe
            MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'dot_576
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v4))
            (MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10
               (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Once.Parser.ExprRelation.C_pcm'45'noop_584
               (coe
                  du_atomExpr'8594'add''_230
                  (coe
                     MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_10 (coe v1)
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
                     (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45'TRParen_274)))
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
            (coe
               MAlonzo.Code.Once.Parser.ExprRelation.C_pct'45'done_562
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
-- Once.Grammar.ExprRelRoundtrip.round-trip-rel-expr
d_round'45'trip'45'rel'45'expr_606 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_494
d_round'45'trip'45'rel'45'expr_606 v0 v1
  = coe
      d_rt'45'expr_274 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe C_q'45''91''93'_8)
      (coe MAlonzo.Code.Once.Parser.ExprRelation.C_nqp'45''91''93'_266)
