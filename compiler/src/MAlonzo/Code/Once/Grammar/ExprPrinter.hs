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

module MAlonzo.Code.Once.Grammar.ExprPrinter where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.Printer
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Grammar.ExprPrinter.binOpToken
d_binOpToken_6 ::
  MAlonzo.Code.Once.Grammar.T_BinOp_52 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6
d_binOpToken_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_OpAdd_54
        -> coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48
      MAlonzo.Code.Once.Grammar.C_OpSub_56
        -> coe MAlonzo.Code.Once.Parser.Token.C_TMinus_50
      MAlonzo.Code.Once.Grammar.C_OpMul_58
        -> coe MAlonzo.Code.Once.Parser.Token.C_TStar_52
      MAlonzo.Code.Once.Grammar.C_OpDiv_60
        -> coe MAlonzo.Code.Once.Parser.Token.C_TSlash_54
      MAlonzo.Code.Once.Grammar.C_OpMod_62
        -> coe MAlonzo.Code.Once.Parser.Token.C_TPercent_56
      MAlonzo.Code.Once.Grammar.C_OpLt_64
        -> coe MAlonzo.Code.Once.Parser.Token.C_TLt_60
      MAlonzo.Code.Once.Grammar.C_OpLe_66
        -> coe MAlonzo.Code.Once.Parser.Token.C_TLe_62
      MAlonzo.Code.Once.Grammar.C_OpGt_68
        -> coe MAlonzo.Code.Once.Parser.Token.C_TGt_64
      MAlonzo.Code.Once.Grammar.C_OpGe_70
        -> coe MAlonzo.Code.Once.Parser.Token.C_TGe_66
      MAlonzo.Code.Once.Grammar.C_OpEq_72
        -> coe MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
      MAlonzo.Code.Once.Grammar.C_OpNe_74
        -> coe MAlonzo.Code.Once.Parser.Token.C_TNeq_70
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprPrinter.printGExpr
d_printGExpr_8 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_printGExpr_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_EUnit_82
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Grammar.C_EInt_84 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TInt_10 (coe v1)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_EVar_86 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TWord_8 (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_EQualified_88 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TWord_8 (coe v1))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Parser.Token.C_TAt_42)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TWord_8 (coe v2))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Grammar.C_ELam_90 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Parser.Token.C_TLambda_36)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TWord_8 (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe d_printGExpr_8 (coe v2))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
      MAlonzo.Code.Once.Grammar.C_EApp_92 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGExpr_8 (coe v1))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_printGExpr_8 (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.Grammar.C_EPair_94 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGExpr_8 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TComma_38)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe d_printGExpr_8 (coe v2))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Grammar.C_ELet_96 v1 v2
        -> case coe v1 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe d_printGExpr_8 (coe v2))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18) (coe v1)))
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Parser.Token.C_TWord_8
                          (coe ("let" :: Data.Text.Text)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe d_printLetBindings_10 (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                (coe ("in" :: Data.Text.Text)))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe d_printGExpr_8 (coe v2))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.C_EDestruct_98 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Parser.Token.C_TWord_8
                   (coe ("destruct" :: Data.Text.Text)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_printGExpr_8 (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Parser.Token.C_TWord_8
                         (coe ("of" :: Data.Text.Text)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TLBrace_20)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.Parser.Token.C_TWord_8
                               (coe ("Left" :: Data.Text.Text)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TWord_8 (coe v2))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe d_printGExpr_8 (coe v3))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                              (coe ("Right" :: Data.Text.Text)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Token.C_TWord_8 (coe v4))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                                                 (coe
                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                    (coe d_printGExpr_8 (coe v5))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.Token.C_TRBrace_22)
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))
      MAlonzo.Code.Once.Grammar.C_EBinOp_100 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGExpr_8 (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe d_binOpToken_6 (coe v1))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe d_printGExpr_8 (coe v3))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Grammar.C_EUnaryOp_102 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Parser.Token.C_TMinus_50)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_printGExpr_8 (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.Grammar.C_ECompose_104 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGExpr_8 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TDot_46)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe d_printGExpr_8 (coe v2))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Grammar.C_EAnnot_106 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGExpr_8 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TColon_24)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Once.Grammar.Printer.d_printGType_8 (coe v2))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprPrinter.printLetBindings
d_printLetBindings_10 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_printLetBindings_10 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v2 of
                    []
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.Parser.Token.C_TWord_8 (coe v3))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.Parser.Token.C_TEquals_26)
                              (coe d_printGExpr_8 (coe v4)))
                    (:) v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.Parser.Token.C_TWord_8 (coe v3))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.Parser.Token.C_TEquals_26)
                              (coe
                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                 (coe d_printGExpr_8 (coe v4))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40)
                                    (coe d_printLetBindings_10 (coe v2)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprPrinter.ConcreteExpr
d_ConcreteExpr_76 a0 = ()
data T_ConcreteExpr_76
  = C_c'45'e'45'unit_78 | C_c'45'e'45'int_82 | C_c'45'e'45'var_86 |
    C_c'45'e'45'qual_92 | C_c'45'e'45'lam_98 T_ConcreteExpr_76 |
    C_c'45'e'45'app_104 T_ConcreteExpr_76 T_ConcreteExpr_76 |
    C_c'45'e'45'pair_110 T_ConcreteExpr_76 T_ConcreteExpr_76 |
    C_c'45'e'45'annot_116 T_ConcreteExpr_76
                          MAlonzo.Code.Once.Grammar.Printer.T_Concrete_78 |
    C_c'45'e'45'binop_124 T_ConcreteExpr_76 T_ConcreteExpr_76 |
    C_c'45'e'45'unary_130 T_ConcreteExpr_76 |
    C_c'45'e'45'comp_136 T_ConcreteExpr_76 T_ConcreteExpr_76 |
    C_c'45'e'45'let1_144 T_ConcreteExpr_76 T_ConcreteExpr_76 |
    C_c'45'e'45'destr_156 T_ConcreteExpr_76 T_ConcreteExpr_76
                          T_ConcreteExpr_76
