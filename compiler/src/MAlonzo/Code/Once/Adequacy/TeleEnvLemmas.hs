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

module MAlonzo.Code.Once.Adequacy.TeleEnvLemmas where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Adequacy.ResolveFaithful
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.TeleEnvLemmas.σW
d_σW_18 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σW_18 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ResolveFaithful.d_σR_12 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
         (coe v1) (coe v2))
      (coe v3) (coe v4) (coe v5) (coe (0 :: Integer))
-- Once.Adequacy.TeleEnvLemmas.acc-irrel
d_acc'45'irrel_34 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'45'irrel_34 = erased
-- Once.Adequacy.TeleEnvLemmas._.spliceClosed
d_spliceClosed_66 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_spliceClosed_66 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_spliceClosed_66 v2 v3 v4 v5 v6 v7 v8 v9
du_spliceClosed_66 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_spliceClosed_66 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v10 v11 v12 v13
               -> coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_closed_406
                       (coe
                          MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3954
                          (coe v2) (coe v4) (coe v0) (coe v1) (coe (0 :: Integer))
                          (coe
                             MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                (coe (0 :: Integer)) (coe v6) (coe v4))
                             (coe v3) (coe v2)
                             (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62) (coe v9))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v10
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleEnvLemmas._.polyVal
d_polyVal_86 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_polyVal_86 ~v0 ~v1 v2 v3 v4 v5 v6 = du_polyVal_86 v2 v3 v4 v5 v6
du_polyVal_86 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_polyVal_86 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           du_spliceClosed_66 (coe v0) (coe v1) (coe v3) (coe v8) (coe v9)
                           (coe v2) (coe v0 v2)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6158
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                                 (coe v0 v2) (coe v9))
                              (coe v8) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleEnvLemmas._.splice-val
d_splice'45'val_118 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splice'45'val_118 = erased
-- Once.Adequacy.TeleEnvLemmas._.case-val
d_case'45'val_160 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'val_160 = erased
-- Once.Adequacy.TeleEnvLemmas._.refs-lookup
d_refs'45'lookup_196 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refs'45'lookup_196 = erased
-- Once.Adequacy.TeleEnvLemmas._.refs-skip
d_refs'45'skip_230 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refs'45'skip_230 = erased
-- Once.Adequacy.TeleEnvLemmas._.refs-head
d_refs'45'head_258 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refs'45'head_258 = erased
-- Once.Adequacy.TeleEnvLemmas.RefsAgree
d_RefsAgree_272 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_RefsAgree_272 = erased
-- Once.Adequacy.TeleEnvLemmas.envrel-transport
d_envrel'45'transport_296 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_envrel'45'transport_296 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_envrel'45'transport_296 v4 v5 v6 v7
du_envrel'45'transport_296 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_envrel'45'transport_296 v0 v1 v2 v3
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    seq (coe v7)
                    (case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> case coe v3 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe (\ v14 v15 -> coe v12 v14 v15))
                                            (coe
                                               du_envrel'45'transport_296 (coe v5) (coe v9)
                                               (coe v11) (coe v13))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleEnvLemmas.CallsAgree
d_CallsAgree_328 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_CallsAgree_328 = erased
-- Once.Adequacy.TeleEnvLemmas.imprel-transport
d_imprel'45'transport_352 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_imprel'45'transport_352 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_imprel'45'transport_352 v4 v5 v6 v7
du_imprel'45'transport_352 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_imprel'45'transport_352 v0 v1 v2 v3
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v4 v5
        -> coe
             seq (coe v4)
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v3 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                     (coe
                                        du_imprel'45'transport_352 (coe v5) (coe v7) (coe v9)
                                        (coe v11))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleEnvLemmas.refIR-cong
d_refIR'45'cong_394 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  (MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refIR'45'cong_394 = erased
-- Once.Adequacy.TeleEnvLemmas.tableEnv-later
d_tableEnv'45'later_554 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tableEnv'45'later_554 = erased
-- Once.Adequacy.TeleEnvLemmas.callSD-later
d_callSD'45'later_600 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_callSD'45'later_600 = erased
-- Once.Adequacy.TeleEnvLemmas.calls-same
d_calls'45'same_634 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_calls'45'same_634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_calls'45'same_634 v9
du_calls'45'same_634 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_calls'45'same_634 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe du_calls'45'same_634 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
