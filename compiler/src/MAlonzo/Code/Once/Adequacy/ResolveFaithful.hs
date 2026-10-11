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

module MAlonzo.Code.Once.Adequacy.ResolveFaithful where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Poly
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs

-- Once.Adequacy.ResolveFaithful.σ₀
d_σ'8320'_10 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σ'8320'_10 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.SourceDenote.d_internalDefs_90
      (coe v0) (coe v1)
-- Once.Adequacy.ResolveFaithful.σR
d_σR_12 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σR_12 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.SourceDenote.C_defsSem_88 (coe v1)
      (coe
         (\ v6 v7 ->
            coe
              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
              (coe (0 :: Integer))
              (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_8) (coe v7)
              (coe
                 MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3954
                 (coe v7) (coe v2) (coe v3) (coe v4) (coe v5)
                 (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v6))
              (coe v0) (coe d_σ'8320'_10 (coe v0) (coe v1))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Once.Adequacy.ResolveFaithful.sigOp-σ-irrel
d_sigOp'45'σ'45'irrel_46 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigOp'45'σ'45'irrel_46 = erased
-- Once.Adequacy.ResolveFaithful.splice-ctx-indep
d_splice'45'ctx'45'indep_218 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splice'45'ctx'45'indep_218 = erased
-- Once.Adequacy.ResolveFaithful.poly-ctx-indep
d_poly'45'ctx'45'indep_278 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'ctx'45'indep_278 = erased
-- Once.Adequacy.ResolveFaithful.bind2-faithful
d_bind2'45'faithful_332 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bind2'45'faithful_332 = erased
-- Once.Adequacy.ResolveFaithful.binop-le-faithful
d_binop'45'le'45'faithful_394 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_binop'45'le'45'faithful_394 = erased
-- Once.Adequacy.ResolveFaithful._.Ea
d_Ea_426 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_Ea_426 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_Ea_426 v3 v4 v6 v16 v19
du_Ea_426 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  AgdaAny -> AgdaAny
du_Ea_426 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe v2) (coe v1) (coe v3) (coe v4)
-- Once.Adequacy.ResolveFaithful._.Eb
d_Eb_428 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_Eb_428 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 v17 ~v18 v19 ~v20 ~v21
  = du_Eb_428 v3 v5 v6 v17 v19
du_Eb_428 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  AgdaAny -> AgdaAny
du_Eb_428 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe v2) (coe v1) (coe v3) (coe v4)
-- Once.Adequacy.ResolveFaithful.binop-faithful
d_binop'45'faithful_488 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_binop'45'faithful_488 = erased
-- Once.Adequacy.ResolveFaithful.thunk-binop-faithful
d_thunk'45'binop'45'faithful_568 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thunk'45'binop'45'faithful_568 = erased
-- Once.Adequacy.ResolveFaithful._.Ea
d_Ea_602 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_Ea_602 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_Ea_602 v3 v4 v6 v16 v19
du_Ea_602 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  AgdaAny -> AgdaAny
du_Ea_602 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe v2) (coe v1) (coe v3) (coe v4)
-- Once.Adequacy.ResolveFaithful._.Eb
d_Eb_604 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_Eb_604 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 v17 ~v18 v19 ~v20 ~v21
  = du_Eb_604 v3 v5 v6 v17 v19
du_Eb_604 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  AgdaAny -> AgdaAny
du_Eb_604 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe v2) (coe v1) (coe v3) (coe v4)
-- Once.Adequacy.ResolveFaithful._.inner
d_inner_614 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_614 = erased
-- Once.Adequacy.ResolveFaithful.unop-faithful
d_unop'45'faithful_648 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unop'45'faithful_648 = erased
-- Once.Adequacy.ResolveFaithful.resolveExpr-faithful
d_resolveExpr'45'faithful_692 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'faithful_692 = erased
-- Once.Adequacy.ResolveFaithful._.E₁
d_E'8321'_1670 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_E'8321'_1670 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12
               ~v13 v14
  = du_E'8321'_1670 v3 v9 v10 v14
du_E'8321'_1670 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_E'8321'_1670 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76 (coe v2)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12) (coe v1)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45'trans_278
         (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12) (coe v1))
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76 (coe v2)
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12) (coe v1)))
         (coe
            MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''42'One_292
            (coe v1))
         (coe
            MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''43''691'_240
            (coe v2)
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12) (coe v1))))
      (coe v3)
-- Once.Adequacy.ResolveFaithful._.E₂
d_E'8322'_1672 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_E'8322'_1672 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12
               ~v13 v14
  = du_E'8322'_1672 v3 v9 v10 v14
du_E'8322'_1672 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_E'8322'_1672 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76 (coe v2)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12) (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''43''737'_224
         (coe v2)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12) (coe v1)))
      (coe v3)
-- Once.Adequacy.ResolveFaithful._.E₁
d_E'8321'_1706 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_E'8321'_1706 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12
               ~v13 v14
  = du_E'8321'_1706 v3 v9 v10 v14
du_E'8321'_1706 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_E'8321'_1706 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76 (coe v2)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v1)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45'trans_278
         (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v1))
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76 (coe v2)
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v1)))
         (coe
            MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''42'Many_304
            (coe v1))
         (coe
            MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''43''691'_240
            (coe v2)
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v1))))
      (coe v3)
-- Once.Adequacy.ResolveFaithful._.E₂
d_E'8322'_1708 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_E'8322'_1708 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12
               ~v13 v14
  = du_E'8322'_1708 v3 v9 v10 v14
du_E'8322'_1708 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_E'8322'_1708 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76 (coe v2)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''43''737'_224
         (coe v2)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v1)))
      (coe v3)
-- Once.Adequacy.ResolveFaithful._.Eall
d_Eall_1752 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_Eall_1752 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 ~v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 v19
  = du_Eall_1752 v3 v9 v10 v11 v19
du_Eall_1752 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_Eall_1752 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76 (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''43''691'_240
         (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe v4)
-- Once.Adequacy.ResolveFaithful._.Es
d_Es_1754 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_Es_1754 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 v19
  = du_Es_1754 v3 v9 v10 v11 v19
du_Es_1754 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_Es_1754 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76 (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''43''737'_224
         (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe v4)
-- Once.Adequacy.ResolveFaithful._.Eₗ
d_E'8343'_1756 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_E'8343'_1756 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 ~v12
               ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19
  = du_E'8343'_1756 v3 v9 v10 v11 v19
du_E'8343'_1756 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_E'8343'_1756 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v2)
         (coe v3))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''8852''737'_330
         (coe v2) (coe v3))
      (coe du_Eall_1752 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.ResolveFaithful._.Eᵣ
d_E'7523'_1758 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_E'7523'_1758 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 ~v12
               ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19
  = du_E'7523'_1758 v3 v9 v10 v11 v19
du_E'7523'_1758 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_E'7523'_1758 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v2)
         (coe v3))
      (coe v3)
      (coe
         MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''8852''691'_346
         (coe v2) (coe v3))
      (coe du_Eall_1752 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.ResolveFaithful._..extendedlambda0
d_'46'extendedlambda0_1772 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_1772 = erased
