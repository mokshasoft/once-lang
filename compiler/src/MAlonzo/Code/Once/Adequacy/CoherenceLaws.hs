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

module MAlonzo.Code.Once.Adequacy.CoherenceLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.CataRel
import qualified MAlonzo.Code.Once.Adequacy.EnvRel
import qualified MAlonzo.Code.Once.Adequacy.SourceRefl
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.EvalRel
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.Sub
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.Denotation.ValueRelPER
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.FunctorMeaning
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Laws.SubLaws
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.StreamInf
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Adequacy.CoherenceLaws._≈ˢ_
d__'8776''738'__34 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> ()
d__'8776''738'__34 = erased
-- Once.Adequacy.CoherenceLaws._≈_
d__'8776'__64 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T__'8776'__64
  = C_'8776''45'intro_82 (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                          AgdaAny ->
                          AgdaAny ->
                          AgdaAny ->
                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378)
-- Once.Adequacy.CoherenceLaws._≈_.≈-out
d_'8776''45'out_80 ::
  T__'8776'__64 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8776''45'out_80 v0
  = case coe v0 of
      C_'8776''45'intro_82 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLaws.≈-refl
d_'8776''45'refl_94 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> T__'8776'__64
d_'8776''45'refl_94 v0 v1 v2 ~v3 v4 v5
  = du_'8776''45'refl_94 v0 v1 v2 v4 v5
du_'8776''45'refl_94 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> T__'8776'__64
du_'8776''45'refl_94 v0 v1 v2 v3 v4
  = coe
      C_'8776''45'intro_82
      (coe
         (\ v5 v6 ->
            coe
              MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
              (coe v5) (coe v5) (coe v6) (coe v1) (coe v2) (coe v3) (coe v4)))
-- Once.Adequacy.CoherenceLaws.≈-sym
d_'8776''45'sym_116 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8776'__64 -> T__'8776'__64
d_'8776''45'sym_116 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_'8776''45'intro_82 v8
        -> coe
             C_'8776''45'intro_82
             (coe
                (\ v9 v10 v11 v12 v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.ValueRelPER.du_RelS'45'sym_22
                     (coe
                        MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'sym_512
                        (coe v4))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v1) (coe v2) (coe v4) (coe v5) (coe v0) (coe v9) (coe v12))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v1) (coe v2) (coe v4) (coe v6) (coe v0) (coe v9) (coe v11))
                     (coe
                        v8 v9 v10 v12 v11
                        (coe
                           MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'sym_512
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'10214'_'10215''7580'_38
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'8638'__136 (coe v2)
                                 (coe v3)))
                           v11 v12 v13))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLaws.≈-trans
d_'8776''45'trans_146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8776'__64 -> T__'8776'__64 -> T__'8776'__64
d_'8776''45'trans_146 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      C_'8776''45'intro_82 v10
        -> case coe v9 of
             C_'8776''45'intro_82 v11
               -> coe
                    C_'8776''45'intro_82
                    (coe
                       (\ v12 v13 v14 v15 v16 ->
                          coe
                            MAlonzo.Code.Once.Denotation.ValueRelPER.du_RelS'45'trans_86
                            (coe
                               MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'trans_522
                               (coe v4))
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v1) (coe v2) (coe v4) (coe v5) (coe v0) (coe v12) (coe v14))
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v1) (coe v2) (coe v4) (coe v6) (coe v0) (coe v12) (coe v15))
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v1) (coe v2) (coe v4) (coe v7) (coe v0) (coe v12) (coe v15))
                            (coe v10 v12 v13 v14 v15 v16)
                            (coe
                               v11 v12 v13 v15 v15
                               (MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'rightself_530
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'10214'_'10215''7580'_38
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'8638'__136 (coe v2)
                                        (coe v3)))
                                  (coe v14) (coe v15) (coe v16)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLaws.≡→≈
d_'8801''8594''8776'_176 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8776'__64
d_'8801''8594''8776'_176 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7
  = du_'8801''8594''8776'_176 v0 v1 v2 v4 v5
du_'8801''8594''8776'_176 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> T__'8776'__64
du_'8801''8594''8776'_176 v0 v1 v2 v3 v4
  = coe
      du_'8776''45'refl_94 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.CoherenceLaws._.pair-congˢ
d_pair'45'cong'738'_202 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_pair'45'cong'738'_202 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16 v17
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v5) (coe v7) (coe v0) (coe v13)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v5) (coe v8) (coe v0) (coe v13)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v16)))
      (coe
         (\ v18 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe v6) (coe v9) (coe v0) (coe v13)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                         (coe v19))))))
      (coe
         (\ v18 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe v6) (coe v10) (coe v0) (coe v13)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v16)))
              (coe
                 (\ v19 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                         (coe v19))))))
      (coe
         v11 v13 v14
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v16))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v17)))
      (coe
         (\ v18 v19 v20 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe v6) (coe v9) (coe v0) (coe v13)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe v6) (coe v10) (coe v0) (coe v13)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v16)))
              (coe
                 (\ v21 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v21))))
              (coe
                 (\ v21 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v19) (coe v21))))
              (coe
                 v12 v13 v14
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v16))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v17)))
              (coe
                 (\ v21 v22 v23 ->
                    coe
                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v20)
                         (coe v23))))))
-- Once.Adequacy.CoherenceLaws._.add-congˢ
d_add'45'cong'738'_230 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_add'45'cong'738'_230 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.sub-congˢ
d_sub'45'cong'738'_258 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_sub'45'cong'738'_258 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.mul-congˢ
d_mul'45'cong'738'_286 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_mul'45'cong'738'_286 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.div-congˢ
d_div'45'cong'738'_314 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_div'45'cong'738'_314 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.mod-congˢ
d_mod'45'cong'738'_342 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_mod'45'cong'738'_342 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.fadd-congˢ
d_fadd'45'cong'738'_370 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_fadd'45'cong'738'_370 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.fsub-congˢ
d_fsub'45'cong'738'_398 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_fsub'45'cong'738'_398 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.fmul-congˢ
d_fmul'45'cong'738'_426 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_fmul'45'cong'738'_426 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.fdiv-congˢ
d_fdiv'45'cong'738'_454 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_fdiv'45'cong'738'_454 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                      (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.lt-congˢ
d_lt'45'cong'738'_482 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_lt'45'cong'738'_482 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.le-congˢ
d_le'45'cong'738'_510 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_le'45'cong'738'_510 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.gt-congˢ
d_gt'45'cong'738'_538 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_gt'45'cong'738'_538 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.ge-congˢ
d_ge'45'cong'738'_566 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_ge'45'cong'738'_566 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.eq-congˢ
d_eq'45'cong'738'_594 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_eq'45'cong'738'_594 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.ne-congˢ
d_ne'45'cong'738'_622 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_ne'45'cong'738'_622 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v5) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v6) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v17))))))
      (coe
         v9 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v7) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe v8) (coe v0) (coe v11)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14)))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v19))))
              (coe
                 (\ v19 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe v0) (coe v11)
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v19))))
              (coe
                 v10 v11 v12
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v13))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v14))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
                      (coe v11)
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'42'__24
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'43'__26
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                         (coe v19))))))
-- Once.Adequacy.CoherenceLaws._.neg-congˢ
d_neg'45'cong'738'_644 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_neg'45'cong'738'_644 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_neg'45'cong'738'_644 v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11
du_neg'45'cong'738'_644 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_neg'45'cong'738'_644 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v3) (coe v0) (coe v6) (coe v8))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v4) (coe v0) (coe v6) (coe v9))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v6)
         (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_124))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v6)
         (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_124))
      (coe v5 v6 v7 v8 v9 v10)
      (\ v11 v12 v13 ->
         coe
           MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
           (coe v6) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
           (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
           (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_124) v11)
-- Once.Adequacy.CoherenceLaws._.i2f-congˢ
d_i2f'45'cong'738'_660 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_i2f'45'cong'738'_660 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_i2f'45'cong'738'_660 v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11
du_i2f'45'cong'738'_660 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_i2f'45'cong'738'_660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v3) (coe v0) (coe v6) (coe v8))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe v4) (coe v0) (coe v6) (coe v9))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v6)
         (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v6)
         (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136))
      (coe v5 v6 v7 v8 v9 v10)
      (\ v11 v12 v13 ->
         coe
           MAlonzo.Code.Once.Adequacy.SourceRefl.du_sigOp'45'rel_318 (coe v0)
           (coe v6) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
           (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
           (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136) v11)
-- Once.Adequacy.CoherenceLaws._.coerce-congˢ
d_coerce'45'cong'738'_682 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_coerce'45'cong'738'_682 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
                          v12 v13 v14
  = du_coerce'45'cong'738'_682
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_coerce'45'cong'738'_682 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_coerce'45'cong'738'_682 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v3) (coe v6) (coe v0) (coe v9) (coe v11))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v3) (coe v7) (coe v0) (coe v9) (coe v12))
      (coe
         MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
         (coe v3) (coe v4) (coe v5))
      (coe
         MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
         (coe v3) (coe v4) (coe v5))
      (coe v8 v9 v10 v11 v12 v13)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
         (coe v3) (coe v4) (coe v5))
-- Once.Adequacy.CoherenceLaws._.morph-app-congˢ
d_morph'45'app'45'cong'738'_706 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_morph'45'app'45'cong'738'_706 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v4) (coe v7) (coe v0) (coe v10)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                  (coe v3))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                  (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))))
            (coe v12)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v4) (coe v8) (coe v0) (coe v10)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                  (coe v3))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                  (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))))
            (coe v13)))
      (coe
         (\ v15 ->
            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
              (coe v0)
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v10))
              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v5)) (coe v6)
              (coe v15)))
      (coe
         (\ v15 ->
            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
              (coe v0)
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v10))
              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v5)) (coe v6)
              (coe v15)))
      (coe
         v9 v10 v11
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                  (coe v3))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                  (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))))
            (coe v12))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                  (coe v3))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                  (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                  (coe v3))
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                  (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v1))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))))
            (coe v14)))
      (coe
         MAlonzo.Code.Once.Denotation.EvalRel.d_liftFn'45'rel_1302 (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v10))
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v10))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v11)) (coe v4)
         (coe v5) (coe v6))
-- Once.Adequacy.CoherenceLaws._.app-congˢ
d_app'45'cong'738'_742 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_app'45'cong'738'_742 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16 v17 v18
  = case coe v7 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_fin_42
                         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                   (coe v6))
                (coe v8) (coe v0) (coe v14)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v16)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_fin_42
                         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                   (coe v6))
                (coe v9) (coe v0) (coe v14)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v17)))
             (coe
                (\ v19 -> coe v19 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             (coe
                (\ v19 -> coe v19 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             (coe
                v12 v14 v15
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v16))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v17))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v18)))
             (coe (\ v19 v20 v21 -> v21))
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_fin_42
                         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                   (coe v6))
                (coe v8) (coe v0) (coe v14)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v16)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_fin_42
                         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                   (coe v6))
                (coe v9) (coe v0) (coe v14)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v17)))
             (coe
                MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                (coe
                   MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                   (coe v1) (coe v2) (coe v5) (coe v10) (coe v0) (coe v14)
                   (coe
                      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v4)))
                      (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                               (coe v4)))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                            (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                            (coe v3)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                               (coe v4))))
                      (coe v16))))
             (coe
                MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                (coe
                   MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                   (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v14)
                   (coe
                      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v4)))
                      (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                               (coe v4)))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                            (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                            (coe v3)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                               (coe v4))))
                      (coe v17))))
             (coe
                v12 v14 v15
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v16))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v17))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v18)))
             (coe
                (\ v19 v20 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v1) (coe v2) (coe v5) (coe v10) (coe v0) (coe v14)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4))))
                           (coe v16)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v14)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4))))
                           (coe v17)))
                     (coe v19) (coe v20)
                     (coe
                        v13 v14 v15
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4))))
                           (coe v16))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4))))
                           (coe v17))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4))))
                           (coe v18)))))
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_fin_42
                         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                   (coe v6))
                (coe v8) (coe v0) (coe v14)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v16)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_fin_42
                         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                   (coe v6))
                (coe v9) (coe v0) (coe v14)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v17)))
             (coe
                MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                (coe
                   MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                   (coe v1) (coe v2) (coe v5) (coe v10) (coe v0) (coe v14)
                   (coe
                      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v4)))
                      (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                               (coe v4)))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                            (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                            (coe v3)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                               (coe v4))))
                      (coe v16))))
             (coe
                MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                (coe
                   MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                   (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v14)
                   (coe
                      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v4)))
                      (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                               (coe v4)))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                            (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                            (coe v3)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                               (coe v4))))
                      (coe v17))))
             (coe
                v12 v14 v15
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v16))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v17))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v4)))
                   (coe v18)))
             (coe
                (\ v19 v20 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v1) (coe v2) (coe v5) (coe v10) (coe v0) (coe v14)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4))))
                           (coe v16)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v14)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4))))
                           (coe v17)))
                     (coe v19) (coe v20)
                     (coe
                        v13 v14 v15
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4))))
                           (coe v16))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4))))
                           (coe v17))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                    (coe v4))))
                           (coe v18)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLaws._.effApp-congˢ
d_effApp'45'cong'738'_804 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_effApp'45'cong'738'_804 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11
                          v12 v13 v14 v15 v16 v17 v18 v19
  = du_effApp'45'cong'738'_804
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
du_effApp'45'cong'738'_804 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_effApp'45'cong'738'_804 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14 v15 v16 v17 v18
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
      (coe
         (\ v19 v20 v21 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                    (coe v6))
                 (coe v8) (coe v0) (coe v14)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v3)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v16)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                    (coe v6))
                 (coe v9) (coe v0) (coe v14)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v3)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v17)))
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2) (coe v5) (coe v10) (coe v0) (coe v14)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v16))))
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v14)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v17))))
              (coe
                 v12 v14 v15
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v3)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v16))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v3)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v17))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v3)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v18)))
              (coe
                 (\ v22 v23 ->
                    coe
                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                      (coe
                         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                         (coe v1) (coe v2) (coe v5) (coe v10) (coe v0) (coe v14)
                         (coe
                            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                            (coe v4)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                  (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                  (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                            (coe v16)))
                      (coe
                         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                         (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v14)
                         (coe
                            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                            (coe v4)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                  (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                  (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                            (coe v17)))
                      (coe v22) (coe v23)
                      (coe
                         v13 v14 v15
                         (coe
                            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                            (coe v4)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                  (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                  (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                            (coe v16))
                         (coe
                            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                            (coe v4)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                  (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                  (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                            (coe v17))
                         (coe
                            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                            (coe v4)
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                  (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                  (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                            (coe v18)))))))
-- Once.Adequacy.CoherenceLaws._.comp-congˢ
d_comp'45'cong'738'_842 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_comp'45'cong'738'_842 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
            (coe v7))
         (coe v9) (coe v0) (coe v15)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v17)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
            (coe v7))
         (coe v10) (coe v0) (coe v15)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v18)))
      (coe
         (\ v20 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v6))
                 (coe v11) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v17)))
              (coe
                 (\ v21 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v22 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v21 v22) (coe v20)))))))
      (coe
         (\ v20 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v6))
                 (coe v12) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v18)))
              (coe
                 (\ v21 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v22 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v21 v22) (coe v20)))))))
      (coe
         v13 v15 v16
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v17))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v18))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v19)))
      (coe
         (\ v20 v21 v22 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v6))
                 (coe v11) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v17)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v6))
                 (coe v12) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v18)))
              (coe
                 (\ v23 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v24 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v23 v24) (coe v20)))))
              (coe
                 (\ v23 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v24 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v23 v24) (coe v21)))))
              (coe
                 v14 v15 v16
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v17))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v18))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v19)))
              (coe
                 (\ v23 v24 v25 ->
                    coe
                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                      (coe
                         (\ v26 v27 v28 ->
                            coe
                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                              (coe v23 v26) (coe v24 v27) (coe v20) (coe v21)
                              (coe v25 v26 v27 v28) (coe v22)))))))
-- Once.Adequacy.CoherenceLaws._.copair-congˢ
d_copair'45'cong'738'_880 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_copair'45'cong'738'_880 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15 v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
            (coe v7))
         (coe v9) (coe v0) (coe v15)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v17)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
            (coe v7))
         (coe v10) (coe v0) (coe v15)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v18)))
      (coe
         (\ v20 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v7))
                 (coe v11) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v17)))
              (coe
                 (\ v21 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 v20 v21)))))
      (coe
         (\ v20 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v7))
                 (coe v12) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v18)))
              (coe
                 (\ v21 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 v20 v21)))))
      (coe
         v13 v15 v16
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v17))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v18))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v19)))
      (coe
         (\ v20 v21 v22 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v7))
                 (coe v11) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v17)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v7))
                 (coe v12) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v18)))
              (coe
                 (\ v23 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 v20 v23)))
              (coe
                 (\ v23 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 v21 v23)))
              (coe
                 v14 v15 v16
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v17))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v18))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v19)))
              (coe
                 (\ v23 v24 v25 ->
                    coe
                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                      (coe
                         (\ v26 v27 v28 ->
                            case coe v26 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v29
                                -> case coe v27 of
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v30
                                       -> coe v22 v29 v30 v28
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v29
                                -> case coe v27 of
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v30
                                       -> coe v25 v29 v30 v28
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError))))))
-- Once.Adequacy.CoherenceLaws._.fork-congˢ
d_fork'45'cong'738'_922 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_fork'45'cong'738'_922 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
            (coe v6))
         (coe v9) (coe v0) (coe v15)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v17)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
            (coe v6))
         (coe v10) (coe v0) (coe v15)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v18)))
      (coe
         (\ v20 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v7))
                 (coe v11) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v17)))
              (coe
                 (\ v21 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v22 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v20 v22)
                              (coe
                                 (\ v23 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                      (coe v21 v22)
                                      (coe
                                         (\ v24 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v23) (coe v24))))))))))))
      (coe
         (\ v20 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v7))
                 (coe v12) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v18)))
              (coe
                 (\ v21 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v22 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v20 v22)
                              (coe
                                 (\ v23 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                      (coe v21 v22)
                                      (coe
                                         (\ v24 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v23) (coe v24))))))))))))
      (coe
         v13 v15 v16
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v17))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v18))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v19)))
      (coe
         (\ v20 v21 v22 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v7))
                 (coe v11) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v17)))
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                    (coe v7))
                 (coe v12) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v18)))
              (coe
                 (\ v23 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v24 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v20 v24)
                              (coe
                                 (\ v25 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                      (coe v23 v24)
                                      (coe
                                         (\ v26 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v25) (coe v26))))))))))
              (coe
                 (\ v23 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v24 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v21 v24)
                              (coe
                                 (\ v25 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                      (coe v23 v24)
                                      (coe
                                         (\ v26 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v25) (coe v26))))))))))
              (coe
                 v14 v15 v16
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v17))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v18))
                 (coe
                    MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v19)))
              (coe
                 (\ v23 v24 v25 ->
                    coe
                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                      (coe
                         (\ v26 v27 v28 ->
                            coe
                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                              (coe v20 v26) (coe v21 v27)
                              (coe
                                 (\ v29 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                      (coe v23 v26)
                                      (coe
                                         (\ v30 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v29) (coe v30))))))
                              (coe
                                 (\ v29 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                      (coe v24 v27)
                                      (coe
                                         (\ v30 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v29) (coe v30))))))
                              (coe v22 v26 v27 v28)
                              (coe
                                 (\ v29 v30 v31 ->
                                    coe
                                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                      (coe v23 v26) (coe v24 v27)
                                      (coe
                                         (\ v32 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v29) (coe v32))))
                                      (coe
                                         (\ v32 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v30) (coe v32))))
                                      (coe v25 v26 v27 v28)
                                      (coe
                                         (\ v32 v33 v34 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v31) (coe v34))))))))))))
-- Once.Adequacy.CoherenceLaws._.curry-congˢ
d_curry'45'cong'738'_960 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_curry'45'cong'738'_960 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 v9 v10 v11
                         v12 v13 v14 v15 v16
  = du_curry'45'cong'738'_960
      v0 v1 v2 v4 v5 v6 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_curry'45'cong'738'_960 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_curry'45'cong'738'_960 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
            (coe MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v3) (coe v4))
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
            (coe v5))
         (coe v7) (coe v0) (coe v10) (coe v12))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
            (coe MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v3) (coe v4))
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
            (coe v5))
         (coe v8) (coe v0) (coe v10) (coe v13))
      (coe
         (\ v15 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 (\ v16 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v17 ->
                            coe
                              v15
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                                 (coe v17))))))))
      (coe
         (\ v15 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 (\ v16 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v17 ->
                            coe
                              v15
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                                 (coe v17))))))))
      (coe v9 v10 v11 v12 v13 v14)
      (coe
         (\ v15 v16 v17 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
              (coe
                 (\ v18 v19 v20 ->
                    coe
                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                      (coe
                         (\ v21 v22 v23 ->
                            coe
                              v17
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v21))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v19) (coe v22))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v20)
                                 (coe v23))))))))
-- Once.Adequacy.CoherenceLaws._.cata-congˢ
d_cata'45'cong'738'_990 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_cata'45'cong'738'_990 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
            (coe
               MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v4)
               (coe v5))
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
            (coe v5))
         (coe v8) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
            (coe
               MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v4)
               (coe v5))
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
            (coe v5))
         (coe v9) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538 (coe v4)
                 (coe v7)
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
                    (coe v4) (coe v7)
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                       (coe v16))))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538 (coe v4)
                 (coe v7)
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
                    (coe v4) (coe v7)
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                       (coe v16))))))
      (coe
         v10 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
              (\ v19 v20 v21 ->
                 coe
                   MAlonzo.Code.Once.Adequacy.SourceRefl.du_cata'45'clo'45'rel_24
                   (coe v4) (coe v7) (coe v16) (coe v17) (coe v18) v19)))
-- Once.Adequacy.CoherenceLaws._.ana-congˢ
d_ana'45'cong'738'_1026 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_ana'45'cong'738'_1026 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16
  = du_ana'45'cong'738'_1026
      v0 v1 v2 v3 v4 v5 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_ana'45'cong'738'_1026 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_ana'45'cong'738'_1026 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13 v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v6)))
            (coe
               MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v4)
               (coe v5)))
         (coe v8) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v6)))
            (coe
               MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v4)
               (coe v5)))
         (coe v9) (coe v0) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v14)))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 (\ v17 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Once.Internal.StreamInf.du_anaF'7477'_150 v4
                         (\ v18 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                              (coe
                                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                 (coe v4) (coe v7))
                              (coe v16 v18))
                         v17)))))
      (coe
         (\ v16 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 (\ v17 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Once.Internal.StreamInf.du_anaF'7477'_150 v4
                         (\ v18 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                              (coe
                                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                 (coe v4) (coe v7))
                              (coe v16 v18))
                         v17)))))
      (coe
         v10 v11 v12
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v13))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v15)))
      (coe
         (\ v16 v17 v18 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
              (coe
                 (\ v19 v20 v21 ->
                    coe
                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                      (coe
                         MAlonzo.Code.Once.Adequacy.SourceRefl.du_ana'45'clo'45'rel_64
                         (coe v4) (coe v7) (coe v16) (coe v17) (coe v18) (coe v19) (coe v20)
                         (coe v21))))))
-- Once.Adequacy.CoherenceLaws._.loop-congˢ
d_loop'45'cong'738'_1058 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_loop'45'cong'738'_1058 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.C_fin_42
                  (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
            (coe
               MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v5) (coe v4)))
         (coe v6) (coe v0) (coe v9)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v11)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.C_fin_42
                  (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
            (coe
               MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v5) (coe v4)))
         (coe v7) (coe v0) (coe v9)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v12)))
      (coe
         (\ v14 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_iter'8734'_256 (coe v14))))
      (coe
         (\ v14 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_iter'8734'_256 (coe v14))))
      (coe
         v8 v9 v10
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v11))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v12))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v13)))
      (coe
         (\ v14 v15 v16 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
              (coe
                 (\ v17 v18 v19 ->
                    coe
                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'iter'8734'_622
                      (coe v14) (coe v15) (coe (\ v20 v21 v22 -> v22)) (coe v16)
                      (coe v17) (coe v18) (coe v19)))))
-- Once.Adequacy.CoherenceLaws._.let-congˢ
d_let'45'cong'738'_1100 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_let'45'cong'738'_1100 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16 v17 v18
  = case coe v7 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe
             v13 v14 v15
             (coe
                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                      (coe v3)))
                (coe v4)
                (coe
                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                   (coe v4)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                      (coe v3)))
                (coe v16))
             (coe
                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                      (coe v3)))
                (coe v4)
                (coe
                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                   (coe v4)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                      (coe v3)))
                (coe v17))
             (coe
                MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                      (coe v3)))
                (coe v4)
                (coe
                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                   (coe v4)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                      (coe v3)))
                (coe v18))
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v1) (coe v2) (coe v5) (coe v8) (coe v0) (coe v14)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3))))
                   (coe v16)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v1) (coe v2) (coe v5) (coe v9) (coe v0) (coe v14)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3))))
                   (coe v17)))
             (coe
                (\ v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v1))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v5))
                     (coe v6) (coe v10) (coe v0) (coe v14)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v16))
                        (coe v19))))
             (coe
                (\ v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v1))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v5))
                     (coe v6) (coe v11) (coe v0) (coe v14)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v17))
                        (coe v19))))
             (coe
                v12 v14 v15
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3))))
                   (coe v16))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3))))
                   (coe v17))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3))))
                   (coe v18)))
             (coe
                (\ v19 v20 v21 ->
                   coe
                     v13 v14 v15
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v16))
                        (coe v19))
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v17))
                        (coe v20))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v18))
                        (coe v21))))
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v1) (coe v2) (coe v5) (coe v8) (coe v0) (coe v14)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3))))
                   (coe v16)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v1) (coe v2) (coe v5) (coe v9) (coe v0) (coe v14)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3))))
                   (coe v17)))
             (coe
                (\ v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v1))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v5))
                     (coe v6) (coe v10) (coe v0) (coe v14)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v16))
                        (coe v19))))
             (coe
                (\ v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v1))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v5))
                     (coe v6) (coe v11) (coe v0) (coe v14)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v17))
                        (coe v19))))
             (coe
                v12 v14 v15
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3))))
                   (coe v16))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3))))
                   (coe v17))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3)))
                   (coe v3)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe v4)
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                            (coe v3))))
                   (coe v18)))
             (coe
                (\ v19 v20 v21 ->
                   coe
                     v13 v14 v15
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v16))
                        (coe v19))
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v17))
                        (coe v20))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v7)
                                 (coe v3)))
                           (coe v18))
                        (coe v21))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLaws._.case-congˢ
d_case'45'cong'738'_1162 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_case'45'cong'738'_1162 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v8) (coe v9))
         (coe v11) (coe v0) (coe v20)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                  (coe v5)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                  (coe v5)))
            (coe v22)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v8) (coe v9))
         (coe v12) (coe v0) (coe v20)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                  (coe v5)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                  (coe v5)))
            (coe v23)))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
         (\ v25 ->
            coe
              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
              (coe addInt (coe (1 :: Integer)) (coe v1))
              (coe
                 MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v8))
              (coe v10) (coe v13) (coe v0) (coe v20)
              (coe
                 MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v6)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                       (coe v5))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''737'_330
                       (coe v4) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                             (coe v5)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                             (coe v5)))
                       (coe v22)))
                 (coe v25)))
         (\ v25 ->
            coe
              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
              (coe addInt (coe (1 :: Integer)) (coe v1))
              (coe
                 MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v9))
              (coe v10) (coe v15) (coe v0) (coe v20)
              (coe
                 MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                       (coe v5))
                    (coe v5)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''691'_346
                       (coe v4) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                             (coe v5)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                             (coe v5)))
                       (coe v22)))
                 (coe v25))))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
         (\ v25 ->
            coe
              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
              (coe addInt (coe (1 :: Integer)) (coe v1))
              (coe
                 MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v8))
              (coe v10) (coe v14) (coe v0) (coe v20)
              (coe
                 MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v6)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                       (coe v5))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''737'_330
                       (coe v4) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                             (coe v5)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                             (coe v5)))
                       (coe v23)))
                 (coe v25)))
         (\ v25 ->
            coe
              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
              (coe addInt (coe (1 :: Integer)) (coe v1))
              (coe
                 MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v9))
              (coe v10) (coe v16) (coe v0) (coe v20)
              (coe
                 MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                       (coe v5))
                    (coe v5)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''691'_346
                       (coe v4) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                             (coe v5)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                          (coe v5))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                             (coe v5)))
                       (coe v23)))
                 (coe v25))))
      (coe
         v17 v20 v21
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                  (coe v5)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                  (coe v5)))
            (coe v22))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                  (coe v5)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                  (coe v5)))
            (coe v23))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                  (coe v5)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v4)
                  (coe v5)))
            (coe v24)))
      (coe
         (\ v25 v26 v27 ->
            case coe v25 of
              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v28
                -> case coe v26 of
                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v29
                       -> coe
                            v18 v20 v21
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v6)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                     (coe v4) (coe v5))
                                  (coe v4)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''737'_330
                                     (coe v4) (coe v5))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                     (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                        (coe v4) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe v22)))
                               (coe v28))
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v6)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                     (coe v4) (coe v5))
                                  (coe v4)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''737'_330
                                     (coe v4) (coe v5))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                     (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                        (coe v4) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe v23)))
                               (coe v29))
                            (coe
                               MAlonzo.Code.Once.Adequacy.EnvRel.du_bind'45'rel_132 (coe v6)
                               (coe
                                  MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                     (coe v4) (coe v5))
                                  (coe v4)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''737'_330
                                     (coe v4) (coe v5))
                                  (coe
                                     MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                     (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                        (coe v4) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe v24)))
                               (coe v27))
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v28
                -> case coe v26 of
                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v29
                       -> coe
                            v19 v20 v21
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                     (coe v4) (coe v5))
                                  (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''691'_346
                                     (coe v4) (coe v5))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                     (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                        (coe v4) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe v22)))
                               (coe v28))
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v7)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                     (coe v4) (coe v5))
                                  (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''691'_346
                                     (coe v4) (coe v5))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                     (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                        (coe v4) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe v23)))
                               (coe v29))
                            (coe
                               MAlonzo.Code.Once.Adequacy.EnvRel.du_bind'45'rel_132 (coe v7)
                               (coe
                                  MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                     (coe v4) (coe v5))
                                  (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''691'_346
                                     (coe v4) (coe v5))
                                  (coe
                                     MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                     (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                        (coe v4) (coe v5))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                           (coe v4) (coe v5)))
                                     (coe v24)))
                               (coe v27))
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.CoherenceLaws._.lam-congˢ
d_lam'45'cong'738'_1204 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_lam'45'cong'738'_1204 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                        ~v11
  = du_lam'45'cong'738'_1204 v4 v8
du_lam'45'cong'738'_1204 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  (MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_lam'45'cong'738'_1204 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    (\ v2 v3 v4 v5 v6 v7 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                         (coe v2 v3 v4 v5 v6 v7))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    (\ v2 v3 v4 v5 v6 v7 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                         (coe (\ v8 v9 v10 -> coe v2 v3 v4 v5 v6 v7)))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    (\ v2 v3 v4 v5 v6 v7 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                         (coe (\ v8 v9 v10 -> coe v2 v3 v4 v5 v6 v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe
             seq (coe v1)
             (coe
                (\ v2 v3 v4 v5 v6 v7 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                     (coe
                        (\ v8 v9 v10 ->
                           coe
                             v2 v3 v4
                             (coe
                                MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v0)
                                (coe v5) (coe v8))
                             (coe
                                MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v0)
                                (coe v6) (coe v9))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v10))))))
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             seq (coe v1)
             (coe
                (\ v2 v3 v4 v5 v6 v7 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                     (coe
                        (\ v8 v9 v10 ->
                           coe
                             v2 v3 v4
                             (coe
                                MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v0)
                                (coe v5) (coe v8))
                             (coe
                                MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v0)
                                (coe v6) (coe v9))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v10))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLaws._.coerce-reflˢ
d_coerce'45'refl'738'_1290 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_coerce'45'refl'738'_1290 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_coerce'45'refl'738'_1290 v0 v1 v2 v4 v5 v6 v7 v8 v9 v10
du_coerce'45'refl'738'_1290 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_coerce'45'refl'738'_1290 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
      (coe
         MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
         (coe v3) (coe v3)
         (coe
            MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v3) (coe v4) (coe v0) (coe v5) (coe v7))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v3) (coe v4) (coe v0) (coe v5) (coe v8))
      (coe
         MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
         (coe v5) (coe v5) (coe v6) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v7) (coe v8) (coe v9))
      (coe
         MAlonzo.Code.Once.Denotation.Sub.d_'60''58''45'refl'45'rel_72
         (coe v3))
-- Once.Adequacy.CoherenceLaws._.coerce-transˢ
d_coerce'45'trans'738'_1316 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_coerce'45'trans'738'_1316 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14
  = du_coerce'45'trans'738'_1316
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_coerce'45'trans'738'_1316 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_coerce'45'trans'738'_1316 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
      (coe
         MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
         (coe v4) (coe v5) (coe v7))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v4)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v3 v6 v8)
         (coe v0) (coe v9) (coe v11))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v5)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v3
            (MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
               (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
            v8)
         (coe v0) (coe v9) (coe v12))
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
            (coe v1) (coe v2) (coe v3) (coe v8) (coe v0) (coe v9) (coe v11))
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
            (coe v1) (coe v2) (coe v3) (coe v8) (coe v0) (coe v9) (coe v12))
         (coe
            MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
            (coe v3) (coe v4) (coe v6))
         (coe
            MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
            (coe v3) (coe v5)
            (coe
               MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
               (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)))
         (coe
            MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
            (coe v9) (coe v9) (coe v10) (coe v1) (coe v2) (coe v3) (coe v8)
            (coe v11) (coe v12) (coe v13))
         (coe
            MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'trans'45'rel_174
            (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)))
      (coe (\ v14 v15 v16 -> v16))
-- Once.Adequacy.CoherenceLaws._.coerce-uniqˢ
d_coerce'45'uniq'738'_1350 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_coerce'45'uniq'738'_1350 v0 v1 v2 ~v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_coerce'45'uniq'738'_1350 v0 v1 v2 v4 v5 v7 v8 v9 v10
du_coerce'45'uniq'738'_1350 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_coerce'45'uniq'738'_1350 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
      (coe v7) (coe v7) (coe v8) (coe v1) (coe v2) (coe v4)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v3 v5 v6)
-- Once.Adequacy.CoherenceLaws._.pair-coerceˢ
d_pair'45'coerce'738'_1388 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_pair'45'coerce'738'_1388 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14 v15 v16 v17
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v13)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v13)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v16)))
      (coe
         (\ v18 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe v5) (coe v6) (coe v9) (coe v18))))
      (coe
         (\ v18 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe v8)
                 (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v7 v10 v12)
                 (coe v0) (coe v13)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v15)))
              (coe
                 (\ v19 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                         (coe v19))))))
      (coe
         (\ v18 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2) (coe v7) (coe v12) (coe v0) (coe v13)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v16)))
              (coe
                 (\ v19 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                         (coe v19))))))
      (coe
         (\ v18 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v5) (coe v7))
                 (coe MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v6) (coe v8))
                 (coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v9 v10)
                 (coe v18))))
      (coe
         MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
         (coe v13) (coe v13) (coe v14) (coe v1) (coe v2) (coe v5) (coe v11)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v15))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v16))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v17)))
      (coe
         (\ v18 v19 v20 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
              (coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2) (coe v7) (coe v12) (coe v0) (coe v13)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v15)))
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2) (coe v7) (coe v12) (coe v0) (coe v13)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v16)))
                 (coe
                    (\ v21 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                            (coe v7) (coe v8) (coe v10) (coe v21))))
                 (coe
                    (\ v21 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                               (coe v5) (coe v6) (coe v9) (coe v18))
                            (coe v21))))
                 (coe
                    (\ v21 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v19) (coe v21))))
                 (coe
                    (\ v21 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                            (coe MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v5) (coe v7))
                            (coe MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v6) (coe v8))
                            (coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v9 v10)
                            (coe v21))))
                 (coe
                    MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
                    (coe v13) (coe v13) (coe v14) (coe v1) (coe v2) (coe v7) (coe v12)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v15))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v16))
                    (coe
                       MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v17)))
                 (coe
                    (\ v21 v22 v23 ->
                       coe
                         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                            (coe
                               MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98 v5
                                     v6 v9 v18 v19 v20)
                                  (coe
                                     MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98 v7
                                     v8 v10 v21 v22 v23)))))))))
-- Once.Adequacy.CoherenceLaws._.app-coerceˢ
d_app'45'coerce'738'_1426 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_app'45'coerce'738'_1426 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15 v16
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.C_fin_42
                  (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
            (coe v7))
         (coe v10) (coe v0) (coe v12)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v14)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.C_fin_42
                  (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
            (coe v7))
         (coe v10) (coe v0) (coe v12)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v15)))
      (coe
         (\ v17 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_fin_42
                          (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                    (coe v7))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_fin_42
                          (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                    (coe v7))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v8
                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                       (coe v7))
                    v9)
                 (coe v17))))
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
            (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v12)
            (coe
               MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
               (coe v4)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                  (coe v4)
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                     (coe v4))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                     (coe v3)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
               (coe v14))))
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
            (coe v1) (coe v2) (coe v6)
            (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v5 v8 v11)
            (coe v0) (coe v12)
            (coe
               MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
               (coe v4)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                  (coe v4)
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                     (coe v4))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                     (coe v3)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
               (coe v15))))
      (coe
         MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
         (coe v12) (coe v12) (coe v13) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.C_fin_42
                  (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
            (coe v7))
         (coe v10)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v14))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v15))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v16)))
      (coe
         (\ v17 v18 v19 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
              (coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'691'_776
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v12)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v14)))
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2) (coe v5) (coe v11) (coe v0) (coe v12)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v15)))
                 (coe
                    (\ v20 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                            (coe v5) (coe v6) (coe v8) (coe v20))))
                 (coe v18)
                 (coe
                    MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_fin_42
                             (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                       (coe v7))
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_fin_42
                             (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                       (coe v7))
                    (coe
                       MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v8
                       (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                          (coe v7))
                       v9)
                    (coe v17))
                 (coe
                    MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
                    (coe v12) (coe v12) (coe v13) (coe v1) (coe v2) (coe v5) (coe v11)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v14))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v15))
                    (coe
                       MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v16)))
                 (coe
                    (\ v20 v21 v22 ->
                       coe
                         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
                            (coe
                               MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                               (coe v7) (coe v7)
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                  (coe v7)))
                            (coe
                               v17
                               (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                  (coe v5) (coe v6) (coe v8) (coe v20)))
                            (coe
                               v18
                               (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                  (coe v5) (coe v6) (coe v8) (coe v21)))
                            (coe
                               v19
                               (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                  (coe v5) (coe v6) (coe v8) (coe v20))
                               (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                  (coe v5) (coe v6) (coe v8) (coe v21))
                               (coe
                                  MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98 v5 v6
                                  v8 v20 v21 v22))
                            (coe
                               MAlonzo.Code.Once.Denotation.Sub.d_'60''58''45'refl'45'rel_72
                               (coe v7))))))))
-- Once.Adequacy.CoherenceLaws._.comp-postˢ
d_comp'45'post'738'_1472 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_comp'45'post'738'_1472 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13 v14 v15 v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
            (coe v7))
         (coe v13) (coe v0) (coe v15)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v17)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
            (coe v7))
         (coe v13) (coe v0) (coe v15)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v18)))
      (coe
         (\ v20 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v7))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v8))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                       (coe v6))
                    v10 v11)
                 (coe v20))))
      (coe
         (\ v20 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v6))
                 (coe v14) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v17)))
              (coe
                 (\ v21 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v22 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v21 v22) (coe v20)))))))
      (coe
         (\ v20 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v6))
                 (coe v14) (coe v0) (coe v15)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v18)))
              (coe
                 (\ v21 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v22 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v21 v22) (coe v20)))))))
      (coe
         (\ v20 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v7))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v8))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                       (coe v5))
                    v10 v12)
                 (coe v20))))
      (coe
         MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
         (coe v15) (coe v15) (coe v16) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
            (coe v7))
         (coe v13)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v17))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v18))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v19)))
      (coe
         (\ v20 v21 v22 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
              (coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'691'_776
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                       (coe v6))
                    (coe v14) (coe v0) (coe v15)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v17)))
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                       (coe v6))
                    (coe v14) (coe v0) (coe v15)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v18)))
                 (coe
                    (\ v23 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            (\ v24 ->
                               coe
                                 MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                 (coe v23 v24) (coe v21)))))
                 (coe
                    (\ v23 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                               (coe v7))
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                               (coe v8))
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                               (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                  (coe v5))
                               v10 v12)
                            (coe v23))))
                 (coe
                    (\ v23 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            (\ v24 ->
                               coe
                                 MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                 (coe v23 v24)
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                    (coe
                                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                       (coe v6)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                                       (coe v7))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                       (coe v6)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                                       (coe v8))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                       (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                          (coe v6))
                                       v10 v11)
                                    (coe v20))))))
                 (coe
                    MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
                    (coe v15) (coe v15) (coe v16) (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                       (coe v6))
                    (coe v14)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v17))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v18))
                    (coe
                       MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                       (coe v19)))
                 (coe
                    (\ v23 v24 v25 ->
                       coe
                         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                         (coe
                            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                            (coe
                               (\ v26 v27 v28 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'691'_776
                                    (coe v23 v26)
                                    (coe
                                       v24
                                       (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                          (coe v5) (coe v5)
                                          (coe
                                             MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                             (coe v5))
                                          (coe v27)))
                                    (coe v21)
                                    (coe
                                       (\ v29 ->
                                          coe
                                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                               (coe v7) (coe v8) (coe v10) (coe v29))))
                                    (coe
                                       MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                       (coe
                                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                          (coe v6)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                                          (coe v7))
                                       (coe
                                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                          (coe v6)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                                          (coe v8))
                                       (coe
                                          MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                          (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                             (coe v6))
                                          v10 v11)
                                       (coe v20))
                                    (coe
                                       v25 v26
                                       (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                          (coe v5) (coe v5)
                                          (coe
                                             MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                             (coe v5))
                                          (coe v27))
                                       (coe
                                          MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'refl'45'rel'691'_292
                                          (coe v5) (coe v26) (coe v27) (coe v28)))
                                    (coe
                                       (\ v29 v30 v31 ->
                                          coe
                                            MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                            (coe
                                               MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                               (coe
                                                  v20
                                                  (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                     (coe v6) (coe v6)
                                                     (coe
                                                        MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                        (coe v6))
                                                     (coe v29)))
                                               (coe v21 v30)
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                  (coe v7) (coe v8) (coe v10))
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                  (coe v7) (coe v8) (coe v10))
                                               (coe
                                                  v22
                                                  (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                     (coe v6) (coe v6)
                                                     (coe
                                                        MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                        (coe v6))
                                                     (coe v29))
                                                  v30
                                                  (coe
                                                     MAlonzo.Code.Once.Denotation.Sub.d_'60''58''45'refl'45'rel_72
                                                     v6 v29 v30 v31))
                                               (coe
                                                  MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                                  (coe v7) (coe v8) (coe v10)))))))))))))
-- Once.Adequacy.CoherenceLaws._.comp-preˢ
d_comp'45'pre'738'_1530 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_comp'45'pre'738'_1530 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16 v17 v18 v19 v20 v21
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v7)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v11))
            (coe v9))
         (coe v15) (coe v0) (coe v17)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v19)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v7)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v11))
            (coe v9))
         (coe v15) (coe v0) (coe v17)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v20)))
      (coe
         (\ v22 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v7)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v11))
                    (coe v9))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                    (coe v8))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v12 v13 v14)
                 (coe v22))))
      (coe
         (\ v22 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                    (coe v6))
                 (coe v16) (coe v0) (coe v17)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v19)))
              (coe
                 (\ v23 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v24 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v23 v24) (coe v22)))))))
      (coe
         (\ v22 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v7)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v11))
                    (coe v9))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v7)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                    (coe v8))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                       (coe v7))
                    v13 v14)
                 (coe v22))))
      (coe
         (\ v22 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                    (coe v7))
                 (coe
                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                       (coe v6))
                    (coe
                       MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                       (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                          (coe v5))
                       v12
                       (MAlonzo.Code.Once.Internal.Type.Sub.d_'8849'π'45'refl_80
                          (coe v10)))
                    v16)
                 (coe v0) (coe v17)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                    (coe v20)))
              (coe
                 (\ v23 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v24 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v23 v24) (coe v22)))))))
      (coe
         MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
         (coe v17) (coe v17) (coe v18) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v7)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v11))
            (coe v9))
         (coe v15)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v19))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v20))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3)
               (coe
                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
            (coe v21)))
      (coe
         (\ v22 v23 v24 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
              (coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'691'_776
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                          (coe v6))
                       (coe v16) (coe v0) (coe v17)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v4)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                (coe v4))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                          (coe v19)))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                          (coe v6))
                       (coe v16) (coe v0) (coe v17)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v4)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                (coe v4))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                          (coe v20)))
                    (coe
                       (\ v25 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe
                               MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                                  (coe v6))
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                                  (coe v7))
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                  (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                     (coe v5))
                                  v12
                                  (MAlonzo.Code.Once.Internal.Type.Sub.d_'8849'π'45'refl_80
                                     (coe v10)))
                               (coe v25))))
                    (coe
                       (\ v25 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe
                               (\ v26 ->
                                  coe
                                    MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                    (coe v25 v26)
                                    (coe
                                       MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                       (coe
                                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                          (coe v7)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v11))
                                          (coe v9))
                                       (coe
                                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                          (coe v7)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                                          (coe v8))
                                       (coe
                                          MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                          (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                             (coe v7))
                                          v13 v14)
                                       (coe v23))))))
                    (coe
                       (\ v25 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe
                               (\ v26 ->
                                  coe
                                    MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                    (coe v25 v26)
                                    (coe
                                       MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                       (coe
                                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                          (coe v7)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v11))
                                          (coe v9))
                                       (coe
                                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                          (coe v6)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                                          (coe v8))
                                       (coe
                                          MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v12
                                          v13 v14)
                                       (coe v22))))))
                    (coe
                       MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
                       (coe v17) (coe v17) (coe v18) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                          (coe v6))
                       (coe v16)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v4)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                (coe v4))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                          (coe v19))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v4)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                (coe v4))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                          (coe v20))
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v4)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                (coe v4))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))))
                          (coe v21)))
                    (coe
                       (\ v25 v26 v27 ->
                          coe
                            MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                            (coe
                               MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                               (coe
                                  (\ v28 v29 v30 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'691'_776
                                       (coe v25 v28)
                                       (coe
                                          v26
                                          (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                             (coe v5) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                (coe v5))
                                             (coe v29)))
                                       (coe
                                          (\ v31 ->
                                             coe
                                               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                  (coe v6) (coe v7) (coe v12) (coe v31))))
                                       (coe
                                          MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                          (coe
                                             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                (coe v11))
                                             (coe v9))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                (coe v10))
                                             (coe v8))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                             (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                (coe v7))
                                             v13 v14)
                                          (coe v23))
                                       (coe
                                          MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                          (coe
                                             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                (coe v11))
                                             (coe v9))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                             (coe v6)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                (coe v10))
                                             (coe v8))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v12
                                             v13 v14)
                                          (coe v22))
                                       (coe
                                          v27 v28
                                          (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                             (coe v5) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                (coe v5))
                                             (coe v29))
                                          (coe
                                             MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'refl'45'rel'691'_292
                                             (coe v5) (coe v28) (coe v29) (coe v30)))
                                       (coe
                                          (\ v31 v32 v33 ->
                                             coe
                                               MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                                  (coe
                                                     v22
                                                     (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v6) (coe v7) (coe v12) (coe v31)))
                                                  (coe
                                                     v23
                                                     (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v7) (coe v7)
                                                        (coe
                                                           MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                           (coe v7))
                                                        (coe
                                                           MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe v6) (coe v7) (coe v12) (coe v32))))
                                                  (coe
                                                     MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                     (coe v9) (coe v8) (coe v13))
                                                  (coe
                                                     MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                     (coe v9) (coe v8) (coe v13))
                                                  (coe
                                                     v24
                                                     (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v6) (coe v7) (coe v12) (coe v31))
                                                     (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v7) (coe v7)
                                                        (coe
                                                           MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                           (coe v7))
                                                        (coe
                                                           MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe v6) (coe v7) (coe v12) (coe v32)))
                                                     (coe
                                                        MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'refl'45'rel'691'_292
                                                        (coe v7)
                                                        (coe
                                                           MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe v6) (coe v7) (coe v12) (coe v31))
                                                        (coe
                                                           MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe v6) (coe v7) (coe v12) (coe v32))
                                                        (coe
                                                           MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                                           v6 v7 v12 v31 v32 v33)))
                                                  (coe
                                                     MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                                     (coe v9) (coe v8) (coe v13))))))))))))))
-- Once.Adequacy.CoherenceLaws._.lam-coerceˢ
d_lam'45'coerce'738'_1578 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_lam'45'coerce'738'_1578 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 v10 v11
                          v12 v13 v14 v15 v16
  = du_lam'45'coerce'738'_1578
      v0 v1 v2 v4 v6 v7 v8 v10 v11 v12 v13 v14 v15 v16
du_lam'45'coerce'738'_1578 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_lam'45'coerce'738'_1578 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                (coe
                   (\ v14 v15 v16 ->
                      coe
                        MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                        (coe
                           MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v4))
                           (coe v5) (coe v8) (coe v0) (coe v9) (coe v11))
                        (coe
                           MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v4))
                           (coe v5) (coe v8) (coe v0) (coe v9) (coe v12))
                        (coe
                           MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                           (coe v5) (coe v6) (coe v7))
                        (coe
                           MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                           (coe v5) (coe v6) (coe v7))
                        (coe
                           MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
                           (coe v9) (coe v9) (coe v10)
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Context.C__'44'_'94'__12 v2 v4
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12))
                           (coe v5) (coe v8) (coe v11) (coe v12) (coe v13))
                        (coe
                           MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                           (coe v5) (coe v6) (coe v7)))))
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                (coe
                   (\ v14 v15 v16 ->
                      coe
                        MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                        (coe
                           MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v4))
                           (coe v5) (coe v8) (coe v0) (coe v9)
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v3)
                              (coe v11) (coe v14)))
                        (coe
                           MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v4))
                           (coe v5) (coe v8) (coe v0) (coe v9)
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v3)
                              (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                 (coe v4) (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                    (coe v4))
                                 (coe v15))))
                        (coe
                           MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                           (coe v5) (coe v6) (coe v7))
                        (coe
                           MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                           (coe v5) (coe v6) (coe v7))
                        (coe
                           MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
                           (coe v9) (coe v9) (coe v10)
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Context.C__'44'_'94'__12 v2 v4
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12))
                           (coe v5) (coe v8)
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v3)
                              (coe v11) (coe v14))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v3)
                              (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                 (coe v4) (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                    (coe v4))
                                 (coe v15)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'refl'45'rel'691'_292
                                 (coe v4) (coe v14) (coe v15) (coe v16))))
                        (coe
                           MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                           (coe v5) (coe v6) (coe v7)))))
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                (coe
                   (\ v14 v15 v16 ->
                      coe
                        MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                        (coe
                           MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v4))
                           (coe v5) (coe v8) (coe v0) (coe v9)
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v3)
                              (coe v11) (coe v14)))
                        (coe
                           MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v2) (coe v4))
                           (coe v5) (coe v8) (coe v0) (coe v9)
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v3)
                              (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                 (coe v4) (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                    (coe v4))
                                 (coe v15))))
                        (coe
                           MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                           (coe v5) (coe v6) (coe v7))
                        (coe
                           MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                           (coe v5) (coe v6) (coe v7))
                        (coe
                           MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
                           (coe v9) (coe v9) (coe v10)
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe MAlonzo.Code.Once.Internal.Context.C__'44'_'94'__12 v2 v4 v3)
                           (coe v5) (coe v8)
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v3)
                              (coe v11) (coe v14))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v3)
                              (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                 (coe v4) (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                    (coe v4))
                                 (coe v15)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'refl'45'rel'691'_292
                                 (coe v4) (coe v14) (coe v15) (coe v16))))
                        (coe
                           MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                           (coe v5) (coe v6) (coe v7)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLaws._.copair-coerceˢ
d_copair'45'coerce'738'_1648 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_copair'45'coerce'738'_1648 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 v14 v15 v16 v17 v18
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
            (coe v7))
         (coe v12) (coe v0) (coe v14)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v16)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
            (coe v7))
         (coe v12) (coe v0) (coe v14)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v17)))
      (coe
         (\ v19 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v7))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v8))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                       (coe v5))
                    v10 v11)
                 (coe v19))))
      (coe
         (\ v19 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v8))
                 (coe
                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                       (coe v7))
                    (coe
                       MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                       (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                          (coe v6))
                       v10 v11)
                    v13)
                 (coe v0) (coe v14)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v16)))
              (coe
                 (\ v20 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 v19 v20)))))
      (coe
         (\ v19 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v7))
                 (coe v13) (coe v0) (coe v14)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v17)))
              (coe
                 (\ v20 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 v19 v20)))))
      (coe
         (\ v19 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                    (coe MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v5) (coe v6))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v7))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                    (coe MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v5) (coe v6))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                    (coe v8))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v5) (coe v6)))
                    v10 v11)
                 (coe v19))))
      (coe
         MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
         (coe v14) (coe v14) (coe v15) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
            (coe v7))
         (coe v12)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v16))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v17))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v18)))
      (coe
         (\ v19 v20 v21 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
              (coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                       (coe v7))
                    (coe v13) (coe v0) (coe v14)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v16)))
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                       (coe v7))
                    (coe v13) (coe v0) (coe v14)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v17)))
                 (coe
                    (\ v22 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                               (coe v7))
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                               (coe v8))
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                               (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                  (coe v6))
                               v10 v11)
                            (coe v22))))
                 (coe
                    (\ v22 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                            (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                                  (coe v7))
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                                  (coe v8))
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                  (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                     (coe v5))
                                  v10 v11)
                               (coe v19))
                            v22)))
                 (coe
                    (\ v22 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 v20 v22)))
                 (coe
                    (\ v22 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                               (coe MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v5) (coe v6))
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                               (coe v7))
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                               (coe MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v5) (coe v6))
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                               (coe v8))
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                               (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                  (coe
                                     MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v5) (coe v6)))
                               v10 v11)
                            (coe v22))))
                 (coe
                    MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
                    (coe v14) (coe v14) (coe v15) (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                       (coe v7))
                    (coe v13)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v16))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v17))
                    (coe
                       MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v18)))
                 (coe
                    (\ v22 v23 v24 ->
                       coe
                         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                            (coe
                               MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                               (coe
                                  (\ v25 v26 v27 ->
                                     case coe v25 of
                                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v28
                                         -> case coe v26 of
                                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v29
                                                -> coe
                                                     MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                                     (coe
                                                        v19
                                                        (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe v5) (coe v5)
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                              (coe v5))
                                                           (coe v28)))
                                                     (coe
                                                        MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                        v20 v23
                                                        (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                              (coe v5) (coe v6))
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                              (coe v5) (coe v6))
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                              (coe
                                                                 MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                                 (coe v5) (coe v6)))
                                                           (coe v26)))
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v7) (coe v8) (coe v10))
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v7) (coe v8) (coe v10))
                                                     (coe
                                                        v21
                                                        (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe v5) (coe v5)
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                              (coe v5))
                                                           (coe v28))
                                                        (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe v5) (coe v5)
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                              (coe v5))
                                                           (coe v29))
                                                        (coe
                                                           MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                                           v5 v5
                                                           (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                              (coe v5))
                                                           v28 v29 v27))
                                                     (coe
                                                        MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                                        (coe v7) (coe v8) (coe v10))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v28
                                         -> case coe v26 of
                                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v29
                                                -> coe
                                                     MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                                     (coe
                                                        v22
                                                        (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe v6) (coe v6)
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                              (coe v6))
                                                           (coe v28)))
                                                     (coe
                                                        MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                        v20 v23
                                                        (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                              (coe v5) (coe v6))
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                              (coe v5) (coe v6))
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                              (coe
                                                                 MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                                 (coe v5) (coe v6)))
                                                           (coe v26)))
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v7) (coe v8) (coe v10))
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v7) (coe v8) (coe v10))
                                                     (coe
                                                        v24
                                                        (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe v6) (coe v6)
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                              (coe v6))
                                                           (coe v28))
                                                        (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                           (coe v6) (coe v6)
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                              (coe v6))
                                                           (coe v29))
                                                        (coe
                                                           MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                                           v6 v6
                                                           (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                              (coe v6))
                                                           v28 v29 v27))
                                                     (coe
                                                        MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                                        (coe v7) (coe v8) (coe v10))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError)))))))))
-- Once.Adequacy.CoherenceLaws._.fork-coerceˢ
d_fork'45'coerce'738'_1704 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_fork'45'coerce'738'_1704 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14 v15 v16 v17 v18 v19 v20
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
            (coe v6))
         (coe v14) (coe v0) (coe v16)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v18)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
            (coe v6))
         (coe v14) (coe v0) (coe v16)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v19)))
      (coe
         (\ v21 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                    (coe v6))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                    (coe v7))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                       (coe v5))
                    v11 v13)
                 (coe v21))))
      (coe
         (\ v21 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                    (coe v9))
                 (coe
                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                       (coe v8))
                    (coe
                       MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                       (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                          (coe v5))
                       v12 v13)
                    v15)
                 (coe v0) (coe v16)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v18)))
              (coe
                 (\ v22 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v23 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v21 v23)
                              (coe
                                 (\ v24 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                      (coe v22 v23)
                                      (coe
                                         (\ v25 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v24) (coe v25))))))))))))
      (coe
         (\ v21 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                    (coe v8))
                 (coe v15) (coe v0) (coe v16)
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                       (coe v4))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                       (coe v3) (coe v4))
                    (coe v19)))
              (coe
                 (\ v22 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                      (coe
                         (\ v23 ->
                            coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v21 v23)
                              (coe
                                 (\ v24 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                      (coe v22 v23)
                                      (coe
                                         (\ v25 ->
                                            coe
                                              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v24) (coe v25))))))))))))
      (coe
         (\ v21 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v6) (coe v8)))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v7) (coe v9)))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                       (coe v5))
                    (coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v11 v12)
                    v13)
                 (coe v21))))
      (coe
         MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
         (coe v16) (coe v16) (coe v17) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
            (coe v6))
         (coe v14)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v18))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v19))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
               (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
               (coe v3) (coe v4))
            (coe v20)))
      (coe
         (\ v21 v22 v23 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
              (coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                       (coe v8))
                    (coe v15) (coe v0) (coe v16)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v18)))
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                    (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                       (coe v8))
                    (coe v15) (coe v0) (coe v16)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v19)))
                 (coe
                    (\ v24 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                               (coe v8))
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                               (coe v9))
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                               (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                  (coe v5))
                               v12 v13)
                            (coe v24))))
                 (coe
                    (\ v24 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            (\ v25 ->
                               coe
                                 MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                    (coe
                                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                       (coe v5)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                                       (coe v6))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                       (coe v5)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                                       (coe v7))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                       (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                          (coe v5))
                                       v11 v13)
                                    v21 v25)
                                 (coe
                                    (\ v26 ->
                                       coe
                                         MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                         (coe v24 v25)
                                         (coe
                                            (\ v27 ->
                                               coe
                                                 MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v26) (coe v27))))))))))
                 (coe
                    (\ v24 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            (\ v25 ->
                               coe
                                 MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                 (coe v22 v25)
                                 (coe
                                    (\ v26 ->
                                       coe
                                         MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                         (coe v24 v25)
                                         (coe
                                            (\ v27 ->
                                               coe
                                                 MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v26) (coe v27))))))))))
                 (coe
                    (\ v24 ->
                       coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v6) (coe v8)))
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v7) (coe v9)))
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                               (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                  (coe v5))
                               (coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v11 v12)
                               v13)
                            (coe v24))))
                 (coe
                    MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
                    (coe v16) (coe v16) (coe v17) (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                       (coe v8))
                    (coe v15)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v18))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v19))
                    (coe
                       MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v3)
                          (coe v4))
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                          (coe v3) (coe v4))
                       (coe v20)))
                 (coe
                    (\ v24 v25 v26 ->
                       coe
                         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                            (coe
                               MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                               (coe
                                  (\ v27 v28 v29 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
                                       (coe
                                          v21
                                          (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                             (coe v5) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                (coe v5))
                                             (coe v27)))
                                       (coe
                                          v22
                                          (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                             (coe v5) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                (coe v5))
                                             (coe v28)))
                                       (coe
                                          (\ v30 ->
                                             coe
                                               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                  (coe v6) (coe v7) (coe v11) (coe v30))))
                                       (coe
                                          (\ v30 ->
                                             coe
                                               MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                     (coe v5)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v10))
                                                     (coe v8))
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                     (coe v5)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v10))
                                                     (coe v9))
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                     (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                        (coe v5))
                                                     v12 v13)
                                                  v24 v27)
                                               (coe
                                                  (\ v31 ->
                                                     coe
                                                       MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v30) (coe v31))))))
                                       (coe
                                          (\ v30 ->
                                             coe
                                               MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                               (coe
                                                  v25
                                                  (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                     (coe v5) (coe v5)
                                                     (coe
                                                        MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                        (coe v5))
                                                     (coe v28)))
                                               (coe
                                                  (\ v31 ->
                                                     coe
                                                       MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v30) (coe v31))))))
                                       (coe
                                          (\ v30 ->
                                             coe
                                               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                                     (coe v6) (coe v8))
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                                     (coe v7) (coe v9))
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48
                                                     v11 v12)
                                                  (coe v30))))
                                       (coe
                                          v23
                                          (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                             (coe v5) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                (coe v5))
                                             (coe v27))
                                          (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                             (coe v5) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                (coe v5))
                                             (coe v28))
                                          (coe
                                             MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                             v5 v5
                                             (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                (coe v5))
                                             v27 v28 v29))
                                       (coe
                                          (\ v30 v31 v32 ->
                                             coe
                                               MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
                                                  (coe
                                                     v24
                                                     (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v5) (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                           (coe v5))
                                                        (coe v27)))
                                                  (coe
                                                     v25
                                                     (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v5) (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                           (coe v5))
                                                        (coe v28)))
                                                  (coe
                                                     (\ v33 ->
                                                        coe
                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                          (coe
                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                             (coe v8) (coe v9) (coe v12)
                                                             (coe v33))))
                                                  (coe
                                                     (\ v33 ->
                                                        coe
                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                (coe v6) (coe v7) (coe v11)
                                                                (coe v30))
                                                             (coe v33))))
                                                  (coe
                                                     (\ v33 ->
                                                        coe
                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v31) (coe v33))))
                                                  (coe
                                                     (\ v33 ->
                                                        coe
                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                          (coe
                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                                                (coe v6) (coe v8))
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                                                (coe v7) (coe v9))
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48
                                                                v11 v12)
                                                             (coe v33))))
                                                  (coe
                                                     v26
                                                     (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v5) (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                           (coe v5))
                                                        (coe v27))
                                                     (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v5) (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                           (coe v5))
                                                        (coe v28))
                                                     (coe
                                                        MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                                        v5 v5
                                                        (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                           (coe v5))
                                                        v27 v28 v29))
                                                  (coe
                                                     (\ v33 v34 v35 ->
                                                        coe
                                                          MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                          (coe
                                                             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                                             (coe
                                                                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                                                      v6 v7 v11 v30 v31 v32)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                                                      v8 v9 v12 v33 v34
                                                                      v35))))))))))))))))))
-- Once.Adequacy.CoherenceLaws._.initial-coerceˢ
d_initial'45'coerce'738'_1740 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_initial'45'coerce'738'_1740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_initial'45'coerce'738'_1740
du_initial'45'coerce'738'_1740 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_initial'45'coerce'738'_1740
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
         (coe (\ v0 v1 -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Adequacy.CoherenceLaws.RelF
d_RelF_1760 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_RelF_1760 = erased
-- Once.Adequacy.CoherenceLaws.out-rel
d_out'45'rel_1836 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_out'45'rel_1836 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_out'45'rel_1836 v1 v2 v6 v7 v8
du_out'45'rel_1836 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_out'45'rel_1836 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52 v6
        -> erased
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54 -> coe v4
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_out'45'rel_1836 (coe v9) (coe v7) (coe v11) (coe v12) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_out'45'rel_1836 (coe v10) (coe v8) (coe v11) (coe v12) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_out'45'rel_1836 (coe v9) (coe v7) (coe v11) (coe v13)
                                            (coe v15))
                                         (coe
                                            du_out'45'rel_1836 (coe v10) (coe v8) (coe v12)
                                            (coe v14) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLaws._.Rc
d_Rc_1894 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 -> ()
d_Rc_1894 = erased
-- Once.Adequacy.CoherenceLaws._.Rl
d_Rl_1902 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny -> AgdaAny -> ()
d_Rl_1902 = erased
-- Once.Adequacy.CoherenceLaws._.seq-rel
d_seq'45'rel_1916 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_seq'45'rel_1916 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_seq'45'rel_1916 v1 v2 v3 v4 v5 v6 v7
du_seq'45'rel_1916 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_seq'45'rel_1916 v0 v1 v2 v3 v4 v5 v6
  = case coe v3 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v7
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             (coe v6)
      MAlonzo.Code.Once.Internal.Type.C_Id_14
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Once.Denotation.ValueRelPER.du_RelS'45'pair'691'_280
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v3)
                       (coe v4))
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v3)
                       (coe v5))
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'unfmap'691'_934
                       (coe
                          MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                          (coe v0) (coe v1) (coe v2))
                       (coe
                          MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v3)
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v3)
                          (coe v5))
                       (coe v7))
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v7 v8
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v7)
                              (coe v9))
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v7)
                              (coe v10))
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                           (coe
                              du_seq'45'rel_1916 (coe v0) (coe v1) (coe v2) (coe v7) (coe v9)
                              (coe v10) (coe v6))
                           (coe (\ v11 v12 v13 -> v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v8)
                              (coe v9))
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v8)
                              (coe v10))
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                           (coe
                              du_seq'45'rel_1916 (coe v0) (coe v1) (coe v2) (coe v8) (coe v9)
                              (coe v10) (coe v6))
                           (coe (\ v11 v12 v13 -> v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v7 v8
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v7)
                                     (coe v9))
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v7)
                                     (coe v11))
                                  (coe
                                     (\ v15 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v8) (coe v10))
                                          (coe
                                             (\ v16 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v15) (coe v16))))))
                                  (coe
                                     (\ v15 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v8) (coe v12))
                                          (coe
                                             (\ v16 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v15) (coe v16))))))
                                  (coe
                                     du_seq'45'rel_1916 (coe v0) (coe v1) (coe v2) (coe v7) (coe v9)
                                     (coe v11) (coe v13))
                                  (coe
                                     (\ v15 v16 v17 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v8) (coe v10))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v8) (coe v12))
                                          (coe
                                             (\ v18 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v15) (coe v18))))
                                          (coe
                                             (\ v18 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v16) (coe v18))))
                                          (coe
                                             du_seq'45'rel_1916 (coe v0) (coe v1) (coe v2) (coe v8)
                                             (coe v10) (coe v12) (coe v14))
                                          (coe
                                             (\ v18 v19 v20 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v17) (coe v20))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLaws._.seq-self
d_seq'45'self_1968 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueRel.T_FRel_216
d_seq'45'self_1968 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_seq'45'self_1968 v4 v5 v6 v7
du_seq'45'self_1968 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueRel.T_FRel_216
du_seq'45'self_1968 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v4
        -> coe MAlonzo.Code.Once.Denotation.ValueRel.C_fr'45'K_228
      MAlonzo.Code.Once.Internal.Type.C_Id_14
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe MAlonzo.Code.Once.Denotation.ValueRel.C_fr'45'Id_234 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.C_fr'45'inl_244
                           (coe du_seq'45'self_1968 (coe v4) (coe v6) (coe v7) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.C_fr'45'inr_254
                           (coe du_seq'45'self_1968 (coe v5) (coe v6) (coe v7) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Once.Denotation.ValueRel.C_fr'45'pair_268
                                  (coe du_seq'45'self_1968 (coe v4) (coe v6) (coe v8) (coe v10))
                                  (coe du_seq'45'self_1968 (coe v5) (coe v7) (coe v9) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLaws.layer-rel
d_layer'45'rel_2022 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_layer'45'rel_2022 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_layer'45'rel_2022 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_layer'45'rel_2022 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_layer'45'rel_2022 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = let v9
          = seq
              (coe v1)
              (case coe v8 of
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                   -> coe
                        MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'trans_522 v2
                        (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                           (coe
                              MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                              (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                           (coe
                              MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                              (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                           (coe v4) (coe v6))
                        (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                           (coe
                              MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                              (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                           (coe
                              MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                              (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                           (coe v4)
                           (coe
                              MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                              (coe v2) (coe v3) (coe v5) (coe v7)))
                        v7
                        (coe
                           MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                           (MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                              (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                           (MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                              (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                           v4 v6
                           (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                              (coe v2) (coe v3) (coe v5) (coe v7))
                           v9)
                        (coe
                           du_back_2056 (coe v2) (coe v3) (coe v4) (coe v5) (coe v7)
                           (coe v10))
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C_K_12 v10
           -> case coe v1 of
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52 v12
                  -> coe
                       MAlonzo.Code.Once.Denotation.Sub.d_'60''58''45'refl'45'rel_72 v10
                       (MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                          (coe v10) (coe v12) (coe v6))
                       (MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                          (coe v10) (coe v12) (coe v6))
                       (MAlonzo.Code.Once.Denotation.ValueRel.d_base'45'refl_420
                          (coe v10) (coe v12)
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                             (coe v10) (coe v12) (coe v6)))
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54
                  -> case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> coe
                              MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'trans_522 v2
                              (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                                 (coe v4) (coe v6))
                              (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                                 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                    (coe v2) (coe v3) (coe v5) (coe v7)))
                              v7
                              (coe
                                 MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                 (MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                                 (MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                                 v4 v6
                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                    (coe v2) (coe v3) (coe v5) (coe v7))
                                 v11)
                              (coe
                                 du_back_2056 (coe v2) (coe v3) (coe v4) (coe v5) (coe v7)
                                 (coe v12))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54
                  -> case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                         -> coe
                              MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'trans_522 v2
                              (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                                 (coe v4) (coe v6))
                              (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                                 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                    (coe v2) (coe v3) (coe v5) (coe v7)))
                              v7
                              (coe
                                 MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                 (MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                                 (MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                                 v4 v6
                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                    (coe v2) (coe v3) (coe v5) (coe v7))
                                 v12)
                              (coe
                                 du_back_2056 (coe v2) (coe v3) (coe v4) (coe v5) (coe v7)
                                 (coe v13))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60 v14 v15
                  -> case coe v4 of
                       MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'sum_58 v20 v21
                         -> case coe v6 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v22
                                -> case coe v7 of
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v23
                                       -> coe
                                            du_layer'45'rel_2022 (coe v10) (coe v14) (coe v2)
                                            (coe v3) (coe v20) (coe v5) (coe v22) (coe v23) (coe v8)
                                     _ -> coe v9
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v22
                                -> case coe v7 of
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v23
                                       -> coe
                                            du_layer'45'rel_2022 (coe v11) (coe v15) (coe v2)
                                            (coe v3) (coe v21) (coe v5) (coe v22) (coe v23) (coe v8)
                                     _ -> coe v9
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v9
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54
                  -> case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                         -> coe
                              MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'trans_522 v2
                              (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                                 (coe v4) (coe v6))
                              (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                                 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                    (coe v2) (coe v3) (coe v5) (coe v7)))
                              v7
                              (coe
                                 MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                                 (MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v3))
                                 (MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v2))
                                 v4 v6
                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                    (coe v2) (coe v3) (coe v5) (coe v7))
                                 v12)
                              (coe
                                 du_back_2056 (coe v2) (coe v3) (coe v4) (coe v5) (coe v7)
                                 (coe v13))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66 v14 v15
                  -> case coe v4 of
                       MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v20 v21
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                       -> case coe v8 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      du_layer'45'rel_2022 (coe v10) (coe v14)
                                                      (coe v2) (coe v3) (coe v20) (coe v5) (coe v22)
                                                      (coe v24) (coe v26))
                                                   (coe
                                                      du_layer'45'rel_2022 (coe v11) (coe v15)
                                                      (coe v2) (coe v3) (coe v21) (coe v5) (coe v23)
                                                      (coe v25) (coe v27))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v9
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v9)
-- Once.Adequacy.CoherenceLaws._.back
d_back_2056 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_back_2056 ~v0 v1 v2 v3 v4 ~v5 v6 ~v7 v8
  = du_back_2056 v1 v2 v3 v4 v6 v8
du_back_2056 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_back_2056 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'trans'45'rel_174
              v0 v1
              (MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                 (coe MAlonzo.Code.Once.Internal.Type.C_Id_14) (coe v0))
              v3 v2 v4 v4 v5 in
    coe
      (coe
         MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'trans_522 v0
         (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
            (coe v1) (coe v0) (coe v2)
            (coe
               MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
               (coe v0) (coe v1) (coe v3) (coe v4)))
         (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
            (coe v0) (coe v0)
            (coe
               MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84 (coe v0))
            (coe v4))
         v4 v6
         (coe
            MAlonzo.Code.Once.Denotation.Sub.d_'60''58''45'refl'45'rel_72 v0 v4
            v4 v5))
-- Once.Adequacy.CoherenceLaws.cata-core
d_cata'45'core_2150 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'core_2150 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_cata'45'core_2150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_cata'45'core_2150 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cata'45'core_2150 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe
         MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
         (coe v0))
      (coe
         (\ v13 ->
            coe
              MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                 (coe
                    MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                       (coe
                          MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v0)
                          (coe v2))
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                       (coe v2))
                    (coe
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                       (coe
                          MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v0)
                          (coe v3))
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                       (coe v3))
                    (coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v6 v7 v8)
                    (coe v9)))
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
                 (coe v1) (coe v13))))
      (coe
         (\ v13 ->
            coe
              MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v10))
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
                 (coe v1) (coe v13))))
      (coe
         du_algR_2186 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))
      (coe v12)
-- Once.Adequacy.CoherenceLaws._.self′
d_self'8242'_2180 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_self'8242'_2180 ~v0 v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
                  ~v13
  = du_self'8242'_2180 v1 v3 v5 v10 v11 v12
du_self'8242'_2180 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_self'8242'_2180 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'rightself_530
      (coe
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
         (coe
            MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v0)
            (coe v1))
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2))
         (coe v1))
      (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.CoherenceLaws._.algR
d_algR_2186 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_algR_2186 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13 v14 v15
            v16
  = du_algR_2186 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v16
du_algR_2186 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_algR_2186 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'691'_776
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
            (coe
               MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
               (coe v1) (coe v12)))
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
            (coe
               MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
               (coe v1) (coe v13)))
         (coe
            (\ v15 ->
               coe
                 MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                 (coe
                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v10))
                 (coe
                    (\ v16 ->
                       coe
                         v16
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                            (coe v0) (coe v1) (coe v15))))))
         (coe
            (\ v15 ->
               coe
                 MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                 (coe
                    MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                    (coe v2) (coe v3) (coe v7) (coe v15))))
         (coe
            (\ v15 ->
               coe
                 MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                 (coe
                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                    (coe
                       MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                          (coe
                             MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v0)
                             (coe v2))
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                          (coe v2))
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                          (coe
                             MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v0)
                             (coe v3))
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                          (coe v3))
                       (coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v6 v7 v8)
                       (coe v9)))
                 (coe
                    (\ v16 ->
                       coe
                         v16
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                            (coe v0) (coe v1) (coe v15))))))
         (coe
            du_seq'45'rel_1916 (coe v2) (coe v3) (coe v7) (coe v0)
            (coe
               MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
               (coe v1) (coe v12))
            (coe
               MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
               (coe v1) (coe v13))
            (coe
               du_out'45'rel_1836 (coe v0) (coe v1) (coe v12) (coe v13)
               (coe v14)))
         (coe
            (\ v15 v16 v17 ->
               coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                       (coe
                          v9
                          (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                             (coe
                                MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v0)
                                (coe v3))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v0)
                                (coe v2))
                             (coe v6)
                             (coe
                                MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                                (coe v0) (coe v1) (coe v15))))
                       (coe
                          v10
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                             (coe v0) (coe v1) (coe v16)))
                       (coe
                          MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                          (coe v2) (coe v3) (coe v7))
                       (coe
                          MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                          (coe v2) (coe v3) (coe v7))
                       (coe
                          v11
                          (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                             (coe
                                MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v0)
                                (coe v3))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v0)
                                (coe v2))
                             (coe v6)
                             (coe
                                MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                                (coe v0) (coe v1) (coe v15)))
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                             (coe v0) (coe v1) (coe v16))
                          (coe
                             du_layer'45'rel_2022 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
                             (coe v7) (coe v15) (coe v16) (coe v17)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.SourceRefl.du_'60''58''45'rel_98
                          (coe v2) (coe v3) (coe v7)))))))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
            (coe
               MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
               (coe v1) (coe v13)))
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
            (coe
               MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
               (coe v1) (coe v13)))
         (coe
            (\ v15 ->
               coe
                 MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                 (coe
                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v10))
                 (coe
                    (\ v16 ->
                       coe
                         v16
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                            (coe v0) (coe v1) (coe v15))))))
         (coe
            (\ v15 ->
               coe
                 MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                 (coe
                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v10))
                 (coe
                    (\ v16 ->
                       coe
                         v16
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                            (coe v0) (coe v1) (coe v15))))))
         (coe
            MAlonzo.Code.Once.Denotation.ValueRel.du_seqF'8734''45'rel_1058
            (coe v0)
            (coe
               MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
               (coe v1) (coe v13))
            (coe
               MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
               (coe v1) (coe v13))
            (coe
               du_seq'45'self_1968 (coe v0)
               (coe
                  MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
                  (coe v1) (coe v12))
               (coe
                  MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
                  (coe v1) (coe v13))
               (coe
                  du_out'45'rel_1836 (coe v0) (coe v1) (coe v12) (coe v13)
                  (coe v14))))
         (coe
            (\ v15 v16 v17 ->
               coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                    (coe
                       du_self'8242'_2180 v0 v2 v4 v9 v10 v11
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                          (coe v0) (coe v1) (coe v15))
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                          (coe v0) (coe v1) (coe v16))
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueRel.du_cfD'8315''185''45'rel_1188
                          (coe v0) (coe v1) (coe v15) (coe v16) (coe v17)))))))
-- Once.Adequacy.CoherenceLaws._.cata-coerceˢ
d_cata'45'coerce'738'_2226 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_cata'45'coerce'738'_2226 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14 v15 v16 v17
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'8322'_860
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
            (coe
               MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v4)
               (coe v5))
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
            (coe v5))
         (coe v12) (coe v0) (coe v13)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v15)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
            (coe
               MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v4)
               (coe v5))
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
            (coe v5))
         (coe v12) (coe v0) (coe v13)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v16)))
      (coe
         (\ v18 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                    (coe
                       MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v4)
                       (coe v5))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                    (coe v5))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                    (coe
                       MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v4)
                       (coe v6))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                    (coe v6))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v9 v10 v11)
                 (coe v18))))
      (coe
         (\ v18 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538 (coe v4)
                 (coe v8)
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
                    (coe v4) (coe v8)
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                       (coe v18))))))
      (coe
         (\ v18 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538 (coe v4)
                 (coe v8)
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
                    (coe v4) (coe v8)
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                       (coe v18))))))
      (coe
         (\ v18 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                    (coe MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 (coe v4))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                    (coe v5))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                    (coe MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 (coe v4))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                    (coe v6))
                 (coe
                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                       (coe MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 (coe v4)))
                    v10
                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'8849'π'45'refl_80
                       (coe v7)))
                 (coe v18))))
      (coe
         MAlonzo.Code.Once.Adequacy.SourceRefl.du_SD'45'rel_352 (coe v0)
         (coe v13) (coe v13) (coe v14) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
            (coe
               MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v4)
               (coe v5))
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
            (coe v5))
         (coe v12)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v15))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v16))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v2)
            (coe
               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
            (coe v3)
            (coe
               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
               (coe v3))
            (coe v17)))
      (coe
         (\ v18 v19 v20 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
              (coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                    (coe
                       (\ v21 v22 v23 ->
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               du_cata'45'core_2150 (coe v4) (coe v8) (coe v5) (coe v6) (coe v7)
                               (coe v7) (coe v9) (coe v10) (coe v11) (coe v18) (coe v19) (coe v20)
                               (coe v21))))))))
