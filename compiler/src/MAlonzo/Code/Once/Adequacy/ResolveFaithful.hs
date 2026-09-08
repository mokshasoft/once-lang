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
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ResolveFaithful.resolveExpr-sigOp-closure-faithful
d_resolveExpr'45'sigOp'45'closure'45'faithful_22
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ResolveFaithful.resolveExpr-sigOp-closure-faithful"
-- Once.Adequacy.ResolveFaithful.resolveExpr-poly-splice-faithful
d_resolveExpr'45'poly'45'splice'45'faithful_60
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ResolveFaithful.resolveExpr-poly-splice-faithful"
-- Once.Adequacy.ResolveFaithful.resolveExpr-poly-faithful
d_resolveExpr'45'poly'45'faithful_88 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'poly'45'faithful_88 = erased
-- Once.Adequacy.ResolveFaithful.bind2-faithful
d_bind2'45'faithful_212 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bind2'45'faithful_212 = erased
-- Once.Adequacy.ResolveFaithful.binop-le-faithful
d_binop'45'le'45'faithful_290 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  (AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_binop'45'le'45'faithful_290 = erased
-- Once.Adequacy.ResolveFaithful._.Ea
d_Ea_324 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  (AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> AgdaAny
d_Ea_324 ~v0 ~v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21
  = du_Ea_324 v2 v3 v5 v15 v18
du_Ea_324 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> AgdaAny
du_Ea_324 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe v2) (coe v1) (coe v3) (coe v4)
-- Once.Adequacy.ResolveFaithful._.Eb
d_Eb_326 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  (AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> AgdaAny
d_Eb_326 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21
  = du_Eb_326 v2 v4 v5 v16 v18
du_Eb_326 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> AgdaAny
du_Eb_326 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe v2) (coe v1) (coe v3) (coe v4)
-- Once.Adequacy.ResolveFaithful.binop-faithful
d_binop'45'faithful_396 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_binop'45'faithful_396 = erased
-- Once.Adequacy.ResolveFaithful.thunk-binop-faithful
d_thunk'45'binop'45'faithful_478 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thunk'45'binop'45'faithful_478 = erased
-- Once.Adequacy.ResolveFaithful._.Ea
d_Ea_514 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> AgdaAny
d_Ea_514 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 v15 ~v16 ~v17 ~v18
  = du_Ea_514 v2 v3 v4 v15
du_Ea_514 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Ea_514 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v1)
         (coe v2))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
         (coe v1) (coe v2))
      (coe v3)
-- Once.Adequacy.ResolveFaithful._.Eb
d_Eb_516 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> AgdaAny
d_Eb_516 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 v15 ~v16 ~v17 ~v18
  = du_Eb_516 v2 v3 v4 v15
du_Eb_516 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Eb_516 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v1)
         (coe v2))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
         (coe v1) (coe v2))
      (coe v3)
-- Once.Adequacy.ResolveFaithful._.inner
d_inner_526 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_526 = erased
-- Once.Adequacy.ResolveFaithful.unop-faithful
d_unop'45'faithful_566 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unop'45'faithful_566 = erased
-- Once.Adequacy.ResolveFaithful.resolveExpr-faithful
d_resolveExpr'45'faithful_616 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'faithful_616 = erased
-- Once.Adequacy.ResolveFaithful._.E₁
d_E'8321'_1722 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_E'8321'_1722 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
               v13 ~v14
  = du_E'8321'_1722 v2 v8 v9 v13
du_E'8321'_1722 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'8321'_1722 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
         (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1)))
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
            (coe v1))
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
            (coe v2)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1))))
      (coe v3)
-- Once.Adequacy.ResolveFaithful._.E₂
d_E'8322'_1724 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_E'8322'_1724 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
               v13 ~v14
  = du_E'8322'_1724 v2 v8 v9 v13
du_E'8322'_1724 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'8322'_1724 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
         (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1)))
      (coe v3)
-- Once.Adequacy.ResolveFaithful._.E₁
d_E'8321'_1760 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_E'8321'_1760 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
               v13 ~v14
  = du_E'8321'_1760 v2 v8 v9 v13
du_E'8321'_1760 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'8321'_1760 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
         (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
            (coe v1))
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
            (coe v2)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))))
      (coe v3)
-- Once.Adequacy.ResolveFaithful._.E₂
d_E'8322'_1762 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_E'8322'_1762 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
               v13 ~v14
  = du_E'8322'_1762 v2 v8 v9 v13
du_E'8322'_1762 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'8322'_1762 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
         (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
      (coe v3)
-- Once.Adequacy.ResolveFaithful._.Eall
d_Eall_1808 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_Eall_1808 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 ~v12 ~v13
            ~v14 ~v15 ~v16 ~v17 v18 ~v19
  = du_Eall_1808 v2 v8 v9 v10 v18
du_Eall_1808 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Eall_1808 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
         (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
            (coe v3)))
      (coe v4)
-- Once.Adequacy.ResolveFaithful._.Es
d_Es_1810 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_Es_1810 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 ~v19
  = du_Es_1810 v2 v8 v9 v10 v18
du_Es_1810 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Es_1810 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
            (coe v3)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
         (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
            (coe v3)))
      (coe v4)
-- Once.Adequacy.ResolveFaithful._.Eₗ
d_E'8343'_1812 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_E'8343'_1812 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 ~v12
               ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19
  = du_E'8343'_1812 v2 v8 v9 v10 v18
du_E'8343'_1812 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'8343'_1812 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
         (coe v3))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''737'_428
         (coe v2) (coe v3))
      (coe du_Eall_1808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.ResolveFaithful._.Eᵣ
d_E'7523'_1814 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_E'7523'_1814 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 ~v12
               ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19
  = du_E'7523'_1814 v2 v8 v9 v10 v18
du_E'7523'_1814 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'7523'_1814 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
         (coe v3))
      (coe v3)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''691'_444
         (coe v2) (coe v3))
      (coe du_Eall_1808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.ResolveFaithful._..extendedlambda0
d_'46'extendedlambda0_1828 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_1828 = erased
