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

module MAlonzo.Code.Once.Adequacy.RewriteLinked where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Recognise
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.RewriteLinked.block-linked
d_block'45'linked_20 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_block'45'linked_20 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_block'45'linked_20 v4
du_block'45'linked_20 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 -> AgdaAny
du_block'45'linked_20 v0 = coe du_block'45'decl_58 (coe v0)
-- Once.Adequacy.RewriteLinked._.subst′
d_subst'8242'_46 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> AgdaAny -> AgdaAny
d_subst'8242'_46 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12
  = du_subst'8242'_46 v12
du_subst'8242'_46 :: AgdaAny -> AgdaAny
du_subst'8242'_46 v0 = coe v0
-- Once.Adequacy.RewriteLinked._.block-decl
d_block'45'decl_58 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_block'45'decl_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_block'45'decl_58 v8
du_block'45'decl_58 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 -> AgdaAny
du_block'45'decl_58 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.RewriteLinked.JustLinked
d_JustLinked_92 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_JustLinked_92 = erased
-- Once.Adequacy.RewriteLinked.try-lift-linked
d_try'45'lift'45'linked_112 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
d_try'45'lift'45'linked_112 ~v0 ~v1 v2 v3 v4
  = du_try'45'lift'45'linked_112 v2 v3 v4
du_try'45'lift'45'linked_112 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_try'45'lift'45'linked_112 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IRTy.C_Void_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IRTy.C__'42'__20 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IRTy.C__'43'__22 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> let v3
                 = MAlonzo.Code.Once.Arith.Machine.Rewrite.d_shape'45'of_12
                     (coe v0) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7
                                  = MAlonzo.Code.Once.Arith.Machine.Recognise.d_rb'45'at_486
                                      (coe v5) (coe v0) (coe v1) (coe v2)
                                      (coe
                                         MAlonzo.Code.Once.Arith.Machine.Recognise.du_rb'45'view_398
                                         (coe v2)) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> let v9
                                            = coe
                                                MAlonzo.Code.Once.Arith.Machine.Rewrite.du_has'45'op_38
                                                (coe v8) in
                                      coe
                                        (if coe v9
                                           then coe
                                                  du_block'45'linked_20
                                                  (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                                           else coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> let v3
                 = MAlonzo.Code.Once.Arith.Machine.Rewrite.d_shape'45'of_12
                     (coe v0) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7
                                  = MAlonzo.Code.Once.Arith.Machine.Recognise.d_rbf'45'at_644
                                      (coe v5) (coe v0) (coe v1) (coe v2)
                                      (coe
                                         MAlonzo.Code.Once.Arith.Machine.Recognise.du_rb'45'view_398
                                         (coe v2)) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> let v9
                                            = coe
                                                MAlonzo.Code.Once.Arith.Machine.Rewrite.du_has'45'op_38
                                                (coe v8) in
                                      coe
                                        (if coe v9
                                           then coe
                                                  du_block'45'linked_20
                                                  (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                                           else coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.RewriteLinked.rewrite-ir-linked
d_rewrite'45'ir'45'linked_324 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_rewrite'45'ir'45'linked_324 ~v0 ~v1 v2 v3 v4 v5
  = du_rewrite'45'ir'45'linked_324 v2 v3 v4 v5
du_rewrite'45'ir'45'linked_324 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_rewrite'45'ir'45'linked_324 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.Arith.Machine.Rewrite.d_try'45'lift_64
              (coe v0) (coe v1) (coe v2) in
    coe
      (let v5
             = coe du_try'45'lift'45'linked_112 (coe v0) (coe v1) (coe v2) in
       coe
         (case coe v4 of
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
              -> coe seq (coe v6) (coe v5)
            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
              -> case coe v2 of
                   MAlonzo.Code.Once.IR.C_id_20
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
                     -> case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_rewrite'45'ir'45'linked_324 (coe v7) (coe v1) (coe v9)
                                    (coe v11))
                                 (coe
                                    du_rewrite'45'ir'45'linked_324 (coe v0) (coe v7) (coe v10)
                                    (coe v12))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
                     -> case coe v1 of
                          MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
                            -> case coe v3 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           du_rewrite'45'ir'45'linked_324 (coe v0) (coe v11)
                                           (coe v9) (coe v13))
                                        (coe
                                           du_rewrite'45'ir'45'linked_324 (coe v0) (coe v12)
                                           (coe v10) (coe v14))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Once.IR.C_fst_42
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_snd_48
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_inl_54
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_inr_60
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_case_68 v9 v10
                     -> case coe v0 of
                          MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
                            -> case coe v3 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           du_rewrite'45'ir'45'linked_324 (coe v11) (coe v1)
                                           (coe v9) (coe v13))
                                        (coe
                                           du_rewrite'45'ir'45'linked_324 (coe v12) (coe v1)
                                           (coe v10) (coe v14))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Once.IR.C_terminal_72
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_initial_76
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_curry_84 v9
                     -> case coe v1 of
                          MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
                            -> coe
                                 du_rewrite'45'ir'45'linked_324
                                 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v10))
                                 (coe v11) (coe v9) (coe v3)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Once.IR.C_apply_90
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_In_94 v7
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_out'45'μ_98 v7
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_Cata_106 v7 v10
                     -> case coe v0 of
                          MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
                            -> case coe v12 of
                                 MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                                   -> coe
                                        du_rewrite'45'ir'45'linked_324
                                        (coe
                                           MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                              (coe v13) (coe v1)))
                                        (coe v1) (coe v10) (coe v3)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Once.IR.C_Out_110 v7
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_in'45'ν_114 v7
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_Ana_120 v7 v9
                     -> case coe v1 of
                          MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                            -> coe
                                 du_rewrite'45'ir'45'linked_324 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10)
                                    (coe v0))
                                 (coe v9) (coe v3)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Once.IR.C_const_124 v7 v8
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   MAlonzo.Code.Once.IR.C_SigOp_130 v6 v7 v8 -> coe v3
                   MAlonzo.Code.Once.IR.C_Call_136 v8 -> coe v3
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
