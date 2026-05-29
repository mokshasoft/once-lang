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

module MAlonzo.Code.Once.Grammar.ConcreteDec where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ExprPrinter
import qualified MAlonzo.Code.Once.Grammar.Printer
import qualified MAlonzo.Code.Once.Parser.ExprRelation

-- Once.Grammar.ConcreteDec.concreteType?
d_concreteType'63'_8 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  Maybe MAlonzo.Code.Once.Grammar.Printer.T_Concrete_60
d_concreteType'63'_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_TUnit_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.Printer.C_c'45'unit_62)
      MAlonzo.Code.Once.Grammar.C_TVoid_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.Printer.C_c'45'void_64)
      MAlonzo.Code.Once.Grammar.C_TInt_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.Printer.C_c'45'int_66)
      MAlonzo.Code.Once.Grammar.C_TFloat_16
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.Printer.C_c'45'float_68)
      MAlonzo.Code.Once.Grammar.C_TBuffer_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.Printer.C_c'45'buffer_70)
      MAlonzo.Code.Once.Grammar.C_TString_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.Printer.C_c'45'string_72)
      MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__22 v1 v2 v3
        -> let v4 = d_concreteType'63'_8 (coe v1) in
           coe
             (let v5 = d_concreteType'63'_8 (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Grammar.Printer.C_c'45'fun_92 v6 v7)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C__'8855'__24 v1 v2
        -> let v3 = d_concreteType'63'_8 (coe v1) in
           coe
             (let v4 = d_concreteType'63'_8 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Grammar.Printer.C_c'45'prod_78 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C__'8853'__26 v1 v2
        -> let v3 = d_concreteType'63'_8 (coe v1) in
           coe
             (let v4 = d_concreteType'63'_8 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Grammar.Printer.C_c'45'sum_84 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_TEff_28 v1 v2
        -> let v3 = d_concreteType'63'_8 (coe v1) in
           coe
             (let v4 = d_concreteType'63'_8 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Grammar.Printer.C_c'45'eff_98 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_TVar_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ConcreteDec.concrete?
d_concrete'63'_98 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_70 ->
  Maybe MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78
d_concrete'63'_98 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_EUnit_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unit_80)
      MAlonzo.Code.Once.Grammar.C_EInt_74 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'int_84)
      MAlonzo.Code.Once.Grammar.C_EString_76 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'string_88)
      MAlonzo.Code.Once.Grammar.C_EVar_78 v1
        -> let v2
                 = MAlonzo.Code.Once.Parser.ExprRelation.d_isReserved_6 (coe v1) in
           coe
             (if coe v2
                then coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                else coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'var_92))
      MAlonzo.Code.Once.Grammar.C_EQualified_80 v1 v2
        -> let v3
                 = MAlonzo.Code.Once.Parser.ExprRelation.d_isReserved_6 (coe v1) in
           coe
             (if coe v3
                then coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                else coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'qual_98))
      MAlonzo.Code.Once.Grammar.C_ELam_82 v1 v2
        -> let v3 = d_concrete'63'_98 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'lam_104 v4)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_EApp_84 v1 v2
        -> let v3 = d_concrete'63'_98 (coe v1) in
           coe
             (let v4 = d_concrete'63'_98 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'app_110 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_EPair_86 v1 v2
        -> let v3 = d_concrete'63'_98 (coe v1) in
           coe
             (let v4 = d_concrete'63'_98 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'pair_116 v5
                                    v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_ELet_88 v1 v2
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v4 of
                           []
                             -> let v7 = d_concrete'63'_98 (coe v6) in
                                coe
                                  (let v8 = d_concrete'63'_98 (coe v2) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'let1_150
                                                         v9 v10)
                                               _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                        _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                           (:) v7 v8 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.C_EDestruct_90 v1 v2 v3 v4 v5
        -> let v6 = d_concrete'63'_98 (coe v1) in
           coe
             (let v7 = d_concrete'63'_98 (coe v3) in
              coe
                (let v8 = d_concrete'63'_98 (coe v5) in
                 coe
                   (case coe v6 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                        -> case coe v7 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'destr_162
                                              v9 v10 v11)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
      MAlonzo.Code.Once.Grammar.C_EBinOp_92 v1 v2 v3
        -> let v4 = d_concrete'63'_98 (coe v2) in
           coe
             (let v5 = d_concrete'63'_98 (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'binop_130 v6
                                    v7)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_EUnaryOp_94 v2
        -> let v3 = d_concrete'63'_98 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unary_136 v4)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_ECompose_96 v1 v2
        -> let v3 = d_concrete'63'_98 (coe v1) in
           coe
             (let v4 = d_concrete'63'_98 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'comp_142 v5
                                    v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_EAnnot_98 v1 v2
        -> let v3 = d_concrete'63'_98 (coe v1) in
           coe
             (let v4 = d_concreteType'63'_8 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'annot_122 v5
                                    v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
