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

module MAlonzo.Code.Once.Adequacy.CoherenceHet where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Adequacy.CoherenceLaws
import qualified MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Laws.SubLaws
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Adequacy.CoherenceHet._._≈_
d__'8776'__10 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Adequacy.CoherenceHet._._≈_.≈-out
d_'8776''45'out_132 ::
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8776''45'out_132 v0
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'out_80
      (coe v0)
-- Once.Adequacy.CoherenceHet.RI
d_RI_224 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_RI_224 ~v0 = du_RI_224
du_RI_224 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_RI_224
  = coe MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
-- Once.Adequacy.CoherenceHet.RC
d_RC_226 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_RC_226 ~v0 = du_RC_226
du_RC_226 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_RC_226 = coe MAlonzo.Code.Once.Denotation.Realize.d_realize_20
-- Once.Adequacy.CoherenceHet.uip
d_uip_242 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uip_242 = erased
-- Once.Adequacy.CoherenceHet.as-grade
d_as'45'grade_284 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_as'45'grade_284 = erased
-- Once.Adequacy.CoherenceHet.cod-≡
d_cod'45''8801'_298 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_68 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cod'45''8801'_298 = erased
-- Once.Adequacy.CoherenceHet.Same2
d_Same2_364 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> ()
d_Same2_364 = erased
-- Once.Adequacy.CoherenceHet._≅_
d__'8773'__384 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
newtype T__'8773'__384 = C_'8773'i_402 AgdaAny
-- Once.Adequacy.CoherenceHet._≅_.≅-ty
d_'8773''45'ty_396 ::
  T__'8773'__384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8773''45'ty_396 = erased
-- Once.Adequacy.CoherenceHet._≅_.≅-us
d_'8773''45'us_398 ::
  T__'8773'__384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8773''45'us_398 = erased
-- Once.Adequacy.CoherenceHet._≅_.≅-sem
d_'8773''45'sem_400 :: T__'8773'__384 -> AgdaAny
d_'8773''45'sem_400 v0
  = case coe v0 of
      C_'8773'i_402 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet.≅-of
d_'8773''45'of_408 ::
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  T__'8773'__384
d_'8773''45'of_408 v0 = coe C_'8773'i_402 v0
-- Once.Adequacy.CoherenceHet.≅-refl
d_'8773''45'refl_414 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> T__'8773'__384
d_'8773''45'refl_414 v0 v1 v2 ~v3 v4 v5
  = du_'8773''45'refl_414 v0 v1 v2 v4 v5
du_'8773''45'refl_414 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> T__'8773'__384
du_'8773''45'refl_414 v0 v1 v2 v3 v4
  = coe
      C_'8773'i_402
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8776''45'refl_94
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.CoherenceHet.≅-sym
d_'8773''45'sym_420 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
d_'8773''45'sym_420 v0 v1 v2 v3 v4 ~v5 ~v6 v7 v8 v9
  = du_'8773''45'sym_420 v0 v1 v2 v3 v4 v7 v8 v9
du_'8773''45'sym_420 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
du_'8773''45'sym_420 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_'8773'i_402 v10
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet.≅-≈
d_'8773''45''8776'_428 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_'8773''45''8776'_428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8773''45''8776'_428 v7
du_'8773''45''8776'_428 ::
  T__'8773'__384 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_'8773''45''8776'_428 v0
  = case coe v0 of
      C_'8773'i_402 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.pair-h
d_pair'45'h_448 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_pair'45'h_448 v0 v1 v2 v3 v4 ~v5 ~v6 v7 v8 ~v9 ~v10 v11 v12 v13
                v14 v15 v16
  = du_pair'45'h_448 v0 v1 v2 v3 v4 v7 v8 v11 v12 v13 v14 v15 v16
du_pair'45'h_448 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_pair'45'h_448 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v11 of
      C_'8773'i_402 v15
        -> case coe v12 of
             C_'8773'i_402 v18
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_pair'45'cong_158
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v4) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v15) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.neg-h
d_neg'45'h_458 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
d_neg'45'h_458 v0 v1 v2 ~v3 ~v4 v5 v6 v7
  = du_neg'45'h_458 v0 v1 v2 v5 v6 v7
du_neg'45'h_458 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
du_neg'45'h_458 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_'8773'i_402 v8
        -> coe
             C_'8773'i_402
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_neg'45'cong_764
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.let-h
d_let'45'h_470 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_let'45'h_470 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11 v12 v13
               v14 v15 v16 v17
  = du_let'45'h_470 v0 v1 v2 v3 v4 v6 v7 v8 v12 v13 v14 v15 v16 v17
du_let'45'h_470 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_let'45'h_470 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      C_'8773'i_402 v16
        -> case coe v13 of
             C_'8773'i_402 v19
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_let'45'cong_1314
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v4) (coe v7)
                       (coe v5) (coe v8) (coe v9) (coe v10) (coe v11) (coe v16) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.case-h
d_case'45'h_508 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_case'45'h_508 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 v11 ~v12 v13
                ~v14 v15 ~v16 v17 v18 v19 v20 v21 v22 v23 v24 v25
  = du_case'45'h_508
      v0 v1 v2 v3 v4 v5 v7 v9 v11 v13 v15 v17 v18 v19 v20 v21 v22 v23 v24
      v25
du_case'45'h_508 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_case'45'h_508 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19
  = case coe v17 of
      C_'8773'i_402 v22
        -> case coe v18 of
             C_'8773'i_402 v25
               -> case coe v19 of
                    C_'8773'i_402 v28
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_case'45'cong_1374
                              (coe v0) (coe v1) (coe v2) (coe v6) (coe v7) (coe v8) (coe v9)
                              (coe v10) (coe v3) (coe v4) (coe v5) (coe v11) (coe v12) (coe v13)
                              (coe v14) (coe v15) (coe v16) (coe v22) (coe v25) (coe v28))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.app-h
d_app'45'h_524 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_app'45'h_524 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 v13
               v14 v15 v16 v17 v18
  = du_app'45'h_524 v0 v1 v2 v3 v4 v5 v6 v11 v13 v14 v15 v16 v17 v18
du_app'45'h_524 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_app'45'h_524 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      C_'8773'i_402 v16
        -> case coe v13 of
             C_'8773'i_402 v19
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_app'45'cong_896
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v4) (coe v6)
                       (coe v5) (coe v8) (coe v9) (coe v10) (coe v11) (coe v16) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.effApp-h
d_effApp'45'h_542 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_56 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_effApp'45'h_542 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10 v11 ~v12
                  v13 v14 v15 v16 v17 v18
  = du_effApp'45'h_542
      v0 v1 v2 v3 v4 v5 v9 v11 v13 v14 v15 v16 v17 v18
du_effApp'45'h_542 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_effApp'45'h_542 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      C_'8773'i_402 v16
        -> case coe v13 of
             C_'8773'i_402 v19
               -> coe
                    C_'8773'i_402
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_effApp'45'cong_948
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v4) (coe v5)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v16) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.comp-h
d_comp'45'h_556 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_comp'45'h_556 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 v11 v12 ~v13
                ~v14 v15 v16 v17 v18 v19 v20
  = du_comp'45'h_556
      v0 v1 v2 v3 v4 v5 v6 v11 v12 v15 v16 v17 v18 v19 v20
du_comp'45'h_556 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_comp'45'h_556 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v13 of
      C_'8773'i_402 v17
        -> case coe v14 of
             C_'8773'i_402 v20
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'cong_1002
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8) (coe v4)
                       (coe v6) (coe v5) (coe v9) (coe v10) (coe v11) (coe v12) (coe v17)
                       (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.copair-h
d_copair'45'h_570 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_copair'45'h_570 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9 v10 ~v11 v12 v13
                  v14 v15 v16 v17
  = du_copair'45'h_570
      v0 v1 v2 v3 v4 v5 v6 v9 v10 v12 v13 v14 v15 v16 v17
du_copair'45'h_570 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_copair'45'h_570 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14
  = case coe v13 of
      C_'8773'i_402 v17
        -> case coe v14 of
             C_'8773'i_402 v20
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_copair'45'cong_1056
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v4) (coe v8)
                       (coe v6) (coe v5) (coe v9) (coe v10) (coe v11) (coe v12) (coe v17)
                       (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.fork-h
d_fork'45'h_584 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_fork'45'h_584 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9 v10 ~v11 ~v12 v13
                v14 v15 v16 v17 v18
  = du_fork'45'h_584
      v0 v1 v2 v3 v4 v5 v6 v9 v10 v13 v14 v15 v16 v17 v18
du_fork'45'h_584 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_fork'45'h_584 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v13 of
      C_'8773'i_402 v17
        -> case coe v14 of
             C_'8773'i_402 v20
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fork'45'cong_1110
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v4) (coe v6)
                       (coe v8) (coe v5) (coe v9) (coe v10) (coe v11) (coe v12) (coe v17)
                       (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.curry-h
d_curry'45'h_594 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
d_curry'45'h_594 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 v10 v11 v12
  = du_curry'45'h_594 v0 v1 v2 v4 v5 v6 v7 v10 v11 v12
du_curry'45'h_594 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
du_curry'45'h_594 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_'8773'i_402 v12
        -> coe
             C_'8773'i_402
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_curry'45'cong_1160
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6) (coe v5)
                (coe v7) (coe v8) (coe v12))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.coerce-h
d_coerce'45'h_606 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384
d_coerce'45'h_606 v0 v1 v2 v3 v4 ~v5 ~v6 v7 v8 v9 v10 v11 v12
  = du_coerce'45'h_606 v0 v1 v2 v3 v4 v7 v8 v9 v10 v11 v12
du_coerce'45'h_606 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384
du_coerce'45'h_606 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      C_'8773'i_402 v13
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4 v8 v6)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4 v8 v7)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4 v9 v7)
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'cong_818
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5) (coe v8) (coe v6)
                   (coe v7) (coe v13))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v5) (coe v9) (coe v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.lam-h
d_lam'45'h_622 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8773'__384 -> T__'8773'__384
d_lam'45'h_622 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9 v10 v11 v12 ~v13
               ~v14 v15
  = du_lam'45'h_622 v0 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 v15
du_lam'45'h_622 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
du_lam'45'h_622 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      C_'8773'i_402 v14
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0) (coe v1) (coe v2) (coe v5)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v7)
                      (coe v8))
                   (coe v6))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4 v9)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4 v10)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4 v10)
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_lam'45'cong_1436
                   (coe v4) (coe v7) (coe v14))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8801''8594''8776'_176
                   (coe v0) (coe v1) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v7)
                         (coe v8))
                      (coe v6))
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4 v10)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.lamd-h
d_lamd'45'h_646 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8773'__384 -> T__'8773'__384
d_lamd'45'h_646 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 v10 v11 v12 ~v13
                ~v14 v15
  = du_lamd'45'h_646 v0 v1 v2 v3 v4 v5 v6 v10 v11 v12 v15
du_lamd'45'h_646 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
du_lamd'45'h_646 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      C_'8773'i_402 v13
        -> coe
             du_lam'45'h_622 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
             (coe v7) (coe v8) (coe v9) (coe C_'8773'i_402 v13)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.cata-h
d_cata'45'h_664 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
d_cata'45'h_664 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10 v11 v12
  = du_cata'45'h_664 v0 v1 v2 v3 v4 v5 v7 v8 v9 v10 v11 v12
du_cata'45'h_664 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
du_cata'45'h_664 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      C_'8773'i_402 v14
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                   (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                   (coe v4))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v7 v9)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v7 v10)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8 v10)
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_cata'45'cong_1202
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v4) (coe v5)
                   (coe v7) (coe v9) (coe v10) (coe v14))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8801''8594''8776'_176
                   (coe v0) (coe v1) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                      (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v6))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v4))
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v7 v10)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.ana-h
d_ana'45'h_688 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
d_ana'45'h_688 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_ana'45'h_688 v0 v1 v2 v3 v4 v6 v7 v8 v9 v10 v11 v12 v13
du_ana'45'h_688 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
du_ana'45'h_688 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      C_'8773'i_402 v15
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                   (coe MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v6) (coe v7)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v3 v8 v10)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v3 v8 v11)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v3 v9 v11)
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_ana'45'cong_1244
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v4) (coe v7)
                   (coe v8) (coe v10) (coe v11) (coe v15))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8801''8594''8776'_176
                   (coe v0) (coe v1) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v6) (coe v7)))
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v3 v8 v11)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.loop-h
d_loop'45'h_708 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
d_loop'45'h_708 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 v9
  = du_loop'45'h_708 v0 v1 v2 v3 v4 v5 v7 v8 v9
du_loop'45'h_708 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
du_loop'45'h_708 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_'8773'i_402 v11
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_loop'45'cong_1274
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.catad
d_catad_722 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8773'__384 -> T__'8773'__384
d_catad_722 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8 v9 v10 v11 v12 ~v13 v14
  = du_catad_722 v0 v1 v2 v3 v4 v5 v8 v9 v10 v11 v12 v14
du_catad_722 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
du_catad_722 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_cata'45'h_664 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
-- Once.Adequacy.CoherenceHet._.catad-h
d_catad'45'h_740 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
d_catad'45'h_740 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8 v9 v10 v11 v12 v13
  = du_catad'45'h_740 v0 v1 v2 v3 v4 v5 v8 v9 v10 v11 v12 v13
du_catad'45'h_740 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__384 -> T__'8773'__384
du_catad'45'h_740 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_catad_722 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
-- Once.Adequacy.CoherenceHet._.spine-h
d_spine'45'h_766 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_spine'45'h_766 v0 v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10 ~v11 v12 v13
                 v14 v15 v16 v17 v18
  = du_spine'45'h_766
      v0 v1 v2 v3 v4 v6 v7 v9 v12 v13 v14 v15 v16 v17 v18
du_spine'45'h_766 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_spine'45'h_766 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v13 of
      C_'8773'i_402 v17
        -> case coe v14 of
             C_'8773'i_402 v20
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                       (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6)))
                       (coe v5)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_app_50 v3 v6 v4
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v8 v9)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_app_50 v3 v6 v4
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v8
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v7 v12 v11))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_app_50 v3 v6 v7
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v10 v11)
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_app'45'cong_896
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v4) (coe v5)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8) (coe v8)
                          (coe v9)
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v7 v12 v11)
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8776''45'refl_94
                             (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                (coe v5))
                             (coe v8))
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                             (coe v0) (coe v1) (coe v2) (coe v6) (coe v4)
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v7 v12 v11)
                             (coe v9) (coe v17)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                          (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6)))
                          (coe v5)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_app_50 v3 v6 v4
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v8
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v7 v12 v11))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_app_50 v3 v6 v7
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                   (coe v5))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v12
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v5))
                                   (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10))
                                v8)
                             v11)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_app_50 v3 v6 v7
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v10 v11)
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                             (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6)))
                             (coe v5)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_app_50 v3 v6 v7
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                      (coe v5))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v12
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                         (coe v5))
                                      (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10))
                                   v8)
                                v11)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_app_50 v3 v6 v4
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v8
                                (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v7 v12 v11))
                             (coe
                                MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_app'45'coerce_1628
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4)
                                (coe v5) (coe v12)
                                (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10) (coe v8)
                                (coe v11)))
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_app'45'cong_896
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v5)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                   (coe v5))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v12
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v5))
                                   (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10))
                                v8)
                             (coe v10) (coe v11) (coe v11)
                             (coe
                                MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                                (coe v0) (coe v1) (coe v2) (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                   (coe v5))
                                (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                      (coe v5))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v12
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                         (coe v5))
                                      (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10))
                                   v8)
                                (coe v20))
                             (coe
                                MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8776''45'refl_94
                                (coe v0) (coe v1) (coe v2) (coe v7) (coe v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.gf-h
d_gf'45'h_792 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_gf'45'h_792 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11 v12 ~v13 v14
              v15 v16 v17 v18 v19 v20 v21 v22
  = du_gf'45'h_792
      v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20
      v21 v22
du_gf'45'h_792 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_gf'45'h_792 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16 v17 v18 v19 v20
  = case coe v17 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v28 v29 v30
        -> case coe v19 of
             C_'8773'i_402 v33
               -> case coe v20 of
                    C_'8773'i_402 v36
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                              (coe v0) (coe v1) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v10)))
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v10 v7 v13 v14)
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v10 v7
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v5))
                                       (coe v6))
                                    v18 v12)
                                 v14)
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v10 v4
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v5))
                                       (coe v6))
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v28 v29 v30)
                                    v12)
                                 v15)
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'cong_1002
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v11) (coe v7)
                                 (coe v9) (coe v8) (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v5))
                                       (coe v6))
                                    v18 v12)
                                 (coe v14) (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                                    (coe v0) (coe v1) (coe v2) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v8))
                                       (coe v9))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                          (coe v4)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v5))
                                          (coe v6))
                                       v18 v12)
                                    (coe v13) (coe v33))
                                 (coe
                                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8776''45'refl_94
                                    (coe v0) (coe v1) (coe v2)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v8))
                                       (coe v7))
                                    (coe v14)))
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                                 (coe v0) (coe v1) (coe v2)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v10)))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                    (coe v9))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v10 v7
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                          (coe v4)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v5))
                                          (coe v6))
                                       v18 v12)
                                    v14)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v10 v7
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                          (coe v4)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v5))
                                          (coe v6))
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16 v29
                                          v30)
                                       v12)
                                    v14)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v10 v4
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                          (coe v4)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v5))
                                          (coe v6))
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v28 v29
                                          v30)
                                       v12)
                                    v15)
                                 (coe
                                    MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'cong_1002
                                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v11) (coe v7)
                                    (coe v9) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                          (coe v4)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v5))
                                          (coe v6))
                                       v18 v12)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                          (coe v4)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v5))
                                          (coe v6))
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16 v29
                                          v30)
                                       v12)
                                    (coe v14) (coe v14)
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
                                       (coe v0) (coe v1) (coe v2)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                          (coe v4)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v5))
                                          (coe v6))
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                          (coe v7)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v8))
                                          (coe v9))
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16 v29
                                          v30)
                                       (coe v12))
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8776''45'refl_94
                                       (coe v0) (coe v1) (coe v2)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                          (coe v11)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v8))
                                          (coe v7))
                                       (coe v14)))
                                 (coe
                                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                                    (coe v0) (coe v1) (coe v2)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v10)))
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v8))
                                       (coe v9))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v10 v7
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                             (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                (coe v5))
                                             (coe v6))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16 v29
                                             v30)
                                          v12)
                                       v14)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v10 v4
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                             (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                (coe v5))
                                             (coe v6))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                (coe v4))
                                             v29 v30)
                                          v12)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                             (coe v11)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                (coe v8))
                                             (coe v7))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                (coe v11))
                                             v16
                                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                                (coe v8)))
                                          v14))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v10 v4
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                             (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                (coe v5))
                                             (coe v6))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v28 v29
                                             v30)
                                          v12)
                                       v15)
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'pre_1742
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v11)
                                       (coe v7) (coe v4) (coe v9) (coe v6) (coe v8) (coe v5)
                                       (coe v16) (coe v29) (coe v30) (coe v12) (coe v14))
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'cong_1002
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v11)
                                       (coe v4) (coe v9) (coe v8)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                             (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                (coe v5))
                                             (coe v6))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                (coe v4))
                                             v29 v30)
                                          v12)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                             (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                (coe v5))
                                             (coe v6))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v28 v29
                                             v30)
                                          v12)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                             (coe v11)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                (coe v8))
                                             (coe v7))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                (coe v11))
                                             v16
                                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                                (coe v8)))
                                          v14)
                                       (coe v15)
                                       (coe
                                          MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
                                          (coe v0) (coe v1) (coe v2)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                             (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                (coe v5))
                                             (coe v6))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                             (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                (coe v8))
                                             (coe v9))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v28 v29
                                             v30)
                                          (coe v12))
                                       (coe v36)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.pairc-h
d_pairc'45'h_826 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_pairc'45'h_826 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 ~v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18
  = du_pairc'45'h_826
      v0 v1 v2 v3 v4 v6 v7 v8 v10 v11 v12 v13 v14 v15 v16 v17 v18
du_pairc'45'h_826 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_pairc'45'h_826 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16
  = case coe v15 of
      C_'8773'i_402 v19
        -> case coe v16 of
             C_'8773'i_402 v22
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                       (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                          (coe v6))
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v5) (coe v8))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                          (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v4) (coe v7))
                          (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62 v13 v14)
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v3 v6 v9 v11))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v3 v6
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4 v13 v9)
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v7 v14 v11))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v3 v6 v10 v12)
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                          (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                             (coe v6))
                          (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v5) (coe v8))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v3 v6
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4 v13 v9)
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v7 v14 v11))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v4) (coe v7))
                             (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62 v13 v14)
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v3 v6 v9 v11))
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_pair'45'coerce_1580
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v4) (coe v5)
                             (coe v7) (coe v8) (coe v13) (coe v14) (coe v9) (coe v11)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_pair'45'cong_158
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v5) (coe v8)
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4 v13 v9)
                          (coe v10)
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v7 v14 v11)
                          (coe v12) (coe v19) (coe v22)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.twice-h
d_twice'45'h_850 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384
d_twice'45'h_850 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_twice'45'h_850 v0 v1 v2 v3 v4 v6 v7 v8 v9 v10 v11 v12 v13
du_twice'45'h_850 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384
du_twice'45'h_850 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      C_'8773'i_402 v15
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v6 v10
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4 v9 v7))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4
                   (MAlonzo.Code.Once.Lang.Laws.SubLaws.d_'60''58''45'trans_86
                      (coe v4) (coe v6) (coe v5) (coe v9) (coe v10))
                   v7)
                (coe v8)
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'trans_1502
                   (coe v0) (coe v1) (coe v2) (coe v4) (coe v6) (coe v5) (coe v9)
                   (coe v10) (coe v7))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4
                      (MAlonzo.Code.Once.Lang.Laws.SubLaws.d_'60''58''45'trans_86
                         (coe v4) (coe v6) (coe v5) (coe v9) (coe v10))
                      v7)
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4 v11 v7)
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v5) (coe v11) (coe v7))
                   (coe v15)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.dcsub-h
d_dcsub'45'h_874 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  T__'8773'__384 -> T__'8773'__384
d_dcsub'45'h_874 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17
  = du_dcsub'45'h_874
      v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
du_dcsub'45'h_874 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  T__'8773'__384 -> T__'8773'__384
du_dcsub'45'h_874 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16
  = case coe v16 of
      C_'8773'i_402 v19
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                      v12
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                   v10)
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                      v12
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                         (coe v6))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13
                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v6))
                         v15)
                      v11))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                      (coe v6))
                   (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13 v14 v15)
                   v11)
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'cong_818
                   (coe v0) (coe v1) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v9))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                      v12
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                   (coe v10)
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                         (coe v6))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13
                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v6))
                         v15)
                      v11)
                   (coe v19))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                   (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v9))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                         (coe v6))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                         v12
                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                      (coe
                         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                            (coe v6))
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13
                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v6))
                            v15)
                         v11))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                         (coe v6))
                      (MAlonzo.Code.Once.Lang.Laws.SubLaws.d_'60''58''45'trans_86
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                            (coe v6))
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                            (coe v6))
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                            (coe v9))
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13
                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v6))
                            v15)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                            v12
                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))))
                      v11)
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                         (coe v6))
                      (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13 v14 v15)
                      v11)
                   (coe
                      MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'trans_1502
                      (coe v0) (coe v1) (coe v2)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                         (coe v6))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                         (coe v6))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                         (coe v9))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13
                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v6))
                         v15)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                         v12
                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                      (coe v11))
                   (coe
                      MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
                      (coe v0) (coe v1) (coe v2)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                         (coe v6))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                         (coe v9))
                      (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13 v14 v15)
                      (coe v11))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.lamc-h
d_lamc'45'h_898 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384
d_lamc'45'h_898 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9 v10 v11 v12 ~v13
                ~v14 v15 v16
  = du_lamc'45'h_898 v0 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 v15 v16
du_lamc'45'h_898 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384
du_lamc'45'h_898 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      C_'8773'i_402 v15
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0) (coe v1) (coe v2) (coe v5)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                   (coe v7))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3))
                      v11
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v8)))
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4 v9))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v6 v11 v9))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4 v10)
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                   (coe v0) (coe v1) (coe v2) (coe v5)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                      (coe v7))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v6 v11 v9))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                         (coe v6))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3))
                         v11
                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v8)))
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4 v9))
                   (coe
                      MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_lam'45'coerce_1798
                      (coe v0) (coe v1) (coe v2) (coe v4) (coe v3) (coe v6) (coe v7)
                      (coe v11) (coe v9)))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                   (coe v0) (coe v1) (coe v2) (coe v5)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                      (coe v7))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v6 v11 v9))
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4 v10)
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4 v10)
                   (coe
                      MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_lam'45'cong_1436
                      (coe v4) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                      (coe v15))
                   (coe
                      MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8801''8594''8776'_176
                      (coe v0) (coe v1) (coe v2)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                         (coe v7))
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v4 v10))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.cg-h
d_cg'45'h_926 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_cg'45'h_926 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 ~v11 v12 v13 v14
              v15 v16 v17 v18
  = du_cg'45'h_926
      v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18
du_cg'45'h_926 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_cg'45'h_926 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16
  = case coe v15 of
      C_'8773'i_402 v19
        -> case coe v16 of
             C_'8773'i_402 v22
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                       (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8)))
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                          (coe v7))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v6))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v9))
                             v14
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v8 v4 v10 v12))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v8 v4
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                v14
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v10)
                          v12)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v8 v4 v11 v13)
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                          (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8)))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v7))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v8 v4
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                   v14
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                v10)
                             v12)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v9))
                                v14
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v8 v4 v10 v12))
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'post_1680
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v9) (coe v4)
                             (coe v6) (coe v7) (coe v5) (coe v14)
                             (coe MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))
                             (coe MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))
                             (coe v10) (coe v12)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'cong_1002
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v9) (coe v4)
                          (coe v7) (coe v5)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                v14
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v10)
                          (coe v11) (coe v12) (coe v13) (coe v19) (coe v22)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.cf-h
d_cf'45'h_954 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_cf'45'h_954 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 ~v10 v11 v12 ~v13 v14
              v15 v16 v17 v18 v19 v20 v21 v22 v23 v24
  = du_cf'45'h_954
      v0 v1 v2 v3 v4 v5 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
      v22 v23 v24
du_cf'45'h_954 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_cf'45'h_954 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16 v17 v18 v19 v20 v21
  = case coe v20 of
      C_'8773'i_402 v24
        -> case coe v21 of
             C_'8773'i_402 v27
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                       (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9)))
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                          (coe v11))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v6))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v10))
                             v17
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4 v12 v14))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                v17
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v12)
                          v14)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v7
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                (coe v6))
                             v19 v13)
                          v15)
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                          (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9)))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v11))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                   v17
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                v12)
                             v14)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v10))
                                v17
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4 v12 v14))
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'post_1680
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v10) (coe v4)
                             (coe v6) (coe v11) (coe v5) (coe v17)
                             (coe MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))
                             (coe MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))
                             (coe v12) (coe v14)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                          (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9)))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v11))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                   v17
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                v12)
                             v14)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                   v17
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                      (coe v6))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                         (coe v6))
                                      v18)
                                   v13))
                             v14)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v7
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                   (coe v6))
                                v19 v13)
                             v15)
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'cong_1002
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v10) (coe v4)
                             (coe v11) (coe v5)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                   v17
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                v12)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                   v17
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                      (coe v6))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                         (coe v6))
                                      v18)
                                   v13))
                             (coe v14) (coe v14)
                             (coe
                                MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'cong_818
                                (coe v0) (coe v1) (coe v2)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v11))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                   v17
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                (coe v12)
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                      (coe v6))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                         (coe v6))
                                      v18)
                                   v13)
                                (coe v24))
                             (coe
                                MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8776''45'refl_94
                                (coe v0) (coe v1) (coe v2)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v4))
                                (coe v14)))
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                             (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v11))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                      (coe v6))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                         (coe v4))
                                      v17
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                         (coe v5)))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v8))
                                         (coe v6))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                            (coe v6))
                                         v18)
                                      v13))
                                v14)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                      (coe v6))
                                   (MAlonzo.Code.Once.Lang.Laws.SubLaws.d_'60''58''45'trans_86
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v8))
                                         (coe v6))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v5))
                                         (coe v6))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v5))
                                         (coe v11))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                            (coe v6))
                                         v18)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                            (coe v4))
                                         v17
                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                            (coe v5))))
                                   v13)
                                v14)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v7
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                      (coe v6))
                                   v19 v13)
                                v15)
                             (coe
                                MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'cong_1002
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v10) (coe v4)
                                (coe v11) (coe v5)
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                      (coe v6))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                         (coe v4))
                                      v17
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                         (coe v5)))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v8))
                                         (coe v6))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                            (coe v6))
                                         v18)
                                      v13))
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                      (coe v6))
                                   (MAlonzo.Code.Once.Lang.Laws.SubLaws.d_'60''58''45'trans_86
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v8))
                                         (coe v6))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v5))
                                         (coe v6))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v5))
                                         (coe v11))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                            (coe v6))
                                         v18)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                            (coe v4))
                                         v17
                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                            (coe v5))))
                                   v13)
                                (coe v14) (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'trans_1502
                                   (coe v0) (coe v1) (coe v2)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                                      (coe v6))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                      (coe v6))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                      (coe v11))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                         (coe v6))
                                      v18)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                         (coe v4))
                                      v17
                                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                         (coe v5)))
                                   (coe v13))
                                (coe
                                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8776''45'refl_94
                                   (coe v0) (coe v1) (coe v2)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                      (coe v4))
                                   (coe v14)))
                             (coe
                                MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                                (coe v0) (coe v1) (coe v2)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v11))
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4
                                   (coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v8))
                                         (coe v6))
                                      (MAlonzo.Code.Once.Lang.Laws.SubLaws.d_'60''58''45'trans_86
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v8))
                                            (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v5))
                                            (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v5))
                                            (coe v11))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                               (coe v6))
                                            v18)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                               (coe v4))
                                            v17
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                               (coe v5))))
                                      v13)
                                   v14)
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4
                                   (coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v8))
                                         (coe v6))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16 v17
                                         v18)
                                      v13)
                                   v14)
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v7
                                   (coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v8))
                                         (coe v6))
                                      v19 v13)
                                   v15)
                                (coe
                                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'cong_1002
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v10) (coe v4)
                                   (coe v11) (coe v5)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v8))
                                         (coe v6))
                                      (MAlonzo.Code.Once.Lang.Laws.SubLaws.d_'60''58''45'trans_86
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v8))
                                            (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v5))
                                            (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v5))
                                            (coe v11))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                               (coe v6))
                                            v18)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                               (coe v4))
                                            v17
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                               (coe v5))))
                                      v13)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v8))
                                         (coe v6))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16 v17
                                         v18)
                                      v13)
                                   (coe v14) (coe v14)
                                   (coe
                                      MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
                                      (coe v0) (coe v1) (coe v2)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v8))
                                         (coe v6))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v5))
                                         (coe v11))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16 v17
                                         v18)
                                      (coe v13))
                                   (coe
                                      MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8776''45'refl_94
                                      (coe v0) (coe v1) (coe v2)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v10)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v5))
                                         (coe v4))
                                      (coe v14)))
                                (coe
                                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                                   (coe v0) (coe v1) (coe v2)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                         (coe v9)))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                      (coe v11))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v4
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v8))
                                            (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v16 v17
                                            v18)
                                         v13)
                                      v14)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v7
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v8))
                                            (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                               (coe v7))
                                            v17 v18)
                                         v13)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v10)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v5))
                                            (coe v4))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                               (coe v10))
                                            v16
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                               (coe v5)))
                                         v14))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v3 v9 v7
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v8))
                                            (coe v6))
                                         v19 v13)
                                      v15)
                                   (coe
                                      MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'pre_1742
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v10)
                                      (coe v4) (coe v7) (coe v11) (coe v6) (coe v5) (coe v8)
                                      (coe v16) (coe v17) (coe v18) (coe v13) (coe v14))
                                   (coe
                                      MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_comp'45'cong_1002
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v10)
                                      (coe v7) (coe v11) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v8))
                                            (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                               (coe v7))
                                            v17 v18)
                                         v13)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v8))
                                            (coe v6))
                                         v19 v13)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v10)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v5))
                                            (coe v4))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                               (coe v10))
                                            v16
                                            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                               (coe v5)))
                                         v14)
                                      (coe v15)
                                      (coe
                                         MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
                                         (coe v0) (coe v1) (coe v2)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v8))
                                            (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v5))
                                            (coe v11))
                                         (coe v19) (coe v13))
                                      (coe v27)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.casec-h
d_casec'45'h_984 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_casec'45'h_984 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 ~v11 v12 v13
                 v14 v15 v16 v17 v18
  = du_casec'45'h_984
      v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18
du_casec'45'h_984 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_casec'45'h_984 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16
  = case coe v15 of
      C_'8773'i_402 v19
        -> case coe v16 of
             C_'8773'i_402 v22
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                       (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                          (coe v8))
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                          (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v4) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                          (coe v7))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                             (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v4) (coe v9))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v6))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v4) (coe v9)))
                             v14
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v3 v8 v10 v12))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v3 v8
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                v14
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v10)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v9))
                                v14
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v12))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v3 v8 v11 v13)
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                          (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                             (coe v8))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                             (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v4) (coe v9))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v7))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v3 v8
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                   v14
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                v10)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v9))
                                   v14
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                v12))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v4) (coe v9))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                   (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v4) (coe v9)))
                                v14
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v3 v8 v10 v12))
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_copair'45'coerce_1848
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4) (coe v9)
                             (coe v6) (coe v7) (coe v5) (coe v14)
                             (coe MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))
                             (coe v10) (coe v12)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_copair'45'cong_1056
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4) (coe v9)
                          (coe v7) (coe v5)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                v14
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v10)
                          (coe v11)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v9))
                                v14
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v12)
                          (coe v13) (coe v19) (coe v22)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.casej-h
d_casej'45'h_1040 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  T__'8773'__384 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_casej'45'h_1040 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 v11 ~v12 v13
                  ~v14 v15 ~v16 v17 ~v18 v19 ~v20 v21 v22 v23 v24 v25 v26 v27 v28 v29
                  v30 v31
  = du_casej'45'h_1040
      v0 v1 v2 v3 v4 v5 v7 v9 v11 v13 v15 v17 v19 v21 v22 v23 v24 v25 v26
      v27 v28 v29 v30 v31
du_casej'45'h_1040 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  T__'8773'__384 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_casej'45'h_1040 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
  = case coe v22 of
      C_'8773'i_402 v26
        -> case coe v23 of
             C_'8773'i_402 v29
               -> coe
                    du_casej'45'at_1098 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
                    (coe v18) (coe v19) (coe v20) (coe v21) (coe C_'8773'i_402 v26)
                    (coe C_'8773'i_402 v29)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._._.casej-at
d_casej'45'at_1098 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  T__'8773'__384 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8773'__384 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_casej'45'at_1098 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                   ~v25 v26 v27 v28 v29 ~v30 v31 ~v32 v33 ~v34 v35 ~v36 v37 ~v38 v39
                   v40 ~v41 v42 v43 v44 v45 v46 v47 v48 v49 ~v50 v51 v52 v53
  = du_casej'45'at_1098
      v0 v1 v2 v26 v27 v28 v29 v31 v33 v35 v37 v39 v40 v42 v43 v44 v45
      v46 v47 v48 v49 v51 v52 v53
du_casej'45'at_1098 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  T__'8773'__384 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_casej'45'at_1098 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
  = coe
      du_case'45'h_508 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v12) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v13)
      (coe v14)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v5
         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
            (coe v5) (coe v12)
            (coe MAlonzo.Code.Once.Lang.Type.Sub.d_left_256 (coe v19)))
         v15)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v5
         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
            (coe v5) (coe v12)
            (coe MAlonzo.Code.Once.Lang.Type.Sub.d_left_256 (coe v20)))
         v16)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v11
         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
            (coe v11) (coe v12)
            (coe MAlonzo.Code.Once.Lang.Type.Sub.d_right_258 (coe v19)))
         v17)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v11
         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
            (coe v11) (coe v12)
            (coe MAlonzo.Code.Once.Lang.Type.Sub.d_right_258 (coe v20)))
         v18)
      (coe v21)
      (coe
         du_coerce'45'h_606 (coe v0)
         (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v2 v3
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
         (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v9 v7) (coe v5)
         (coe v12) (coe v15) (coe v16)
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
            (coe v5) (coe v12)
            (coe MAlonzo.Code.Once.Lang.Type.Sub.d_left_256 (coe v19)))
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
            (coe v5) (coe v12)
            (coe MAlonzo.Code.Once.Lang.Type.Sub.d_left_256 (coe v20)))
         (coe v22))
      (coe
         du_coerce'45'h_606 (coe v0)
         (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v2 v4
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
         (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v10 v8) (coe v11)
         (coe v12) (coe v17) (coe v18)
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
            (coe v11) (coe v12)
            (coe MAlonzo.Code.Once.Lang.Type.Sub.d_right_258 (coe v19)))
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
            (coe v11) (coe v12)
            (coe MAlonzo.Code.Once.Lang.Type.Sub.d_right_258 (coe v20)))
         (coe v23))
-- Once.Adequacy.CoherenceHet._.copairj-h
d_copairj'45'h_1130 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_copairj'45'h_1130 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9 v10 ~v11 v12
                    ~v13 v14 ~v15 v16 v17 v18 v19 v20 v21 v22 v23
  = du_copairj'45'h_1130
      v0 v1 v2 v3 v4 v5 v6 v9 v10 v12 v14 v16 v17 v18 v19 v20 v21 v22 v23
du_copairj'45'h_1130 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_copairj'45'h_1130 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                     v14 v15 v16 v17 v18
  = case coe v17 of
      C_'8773'i_402 v21
        -> case coe v18 of
             C_'8773'i_402 v24
               -> coe
                    du_copairj'45'at_1162 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
                    (coe C_'8773'i_402 v21) (coe C_'8773'i_402 v24)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._._.copairj-at
d_copairj'45'at_1162 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_copairj'45'at_1162 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                     ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 v21 v22 v23 ~v24 v25
                     v26 ~v27 v28 v29 ~v30 v31 v32 v33 v34 v35 v36 ~v37 v38 v39
  = du_copairj'45'at_1162
      v0 v1 v2 v20 v21 v22 v23 v25 v26 v28 v29 v31 v32 v33 v34 v35 v36
      v38 v39
du_copairj'45'at_1162 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_copairj'45'at_1162 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15 v16 v17 v18
  = coe
      du_copair'45'h_570 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v10) (coe v7) (coe v8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v6))
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
               (coe v6) (coe v10)
               (coe MAlonzo.Code.Once.Lang.Type.Sub.d_left_256 (coe v15)))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
         v11)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v6))
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
               (coe v6) (coe v10)
               (coe MAlonzo.Code.Once.Lang.Type.Sub.d_left_256 (coe v16)))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
         v12)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v9))
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v8))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
               (coe v9) (coe v10)
               (coe MAlonzo.Code.Once.Lang.Type.Sub.d_right_258 (coe v15)))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
         v13)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v9))
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v8))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
               (coe v9) (coe v10)
               (coe MAlonzo.Code.Once.Lang.Type.Sub.d_right_258 (coe v16)))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
         v14)
      (coe
         du_coerce'45'h_606 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v6))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v10))
         (coe v11) (coe v12)
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
               (coe v6) (coe v10)
               (coe MAlonzo.Code.Once.Lang.Type.Sub.d_left_256 (coe v15)))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
               (coe v6) (coe v10)
               (coe MAlonzo.Code.Once.Lang.Type.Sub.d_left_256 (coe v16)))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
         (coe v17))
      (coe
         du_coerce'45'h_606 (coe v0) (coe v1) (coe v2) (coe v7)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v9))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v10))
         (coe v13) (coe v14)
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v8))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
               (coe v9) (coe v10)
               (coe MAlonzo.Code.Once.Lang.Type.Sub.d_right_258 (coe v15)))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v8))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
               (coe v9) (coe v10)
               (coe MAlonzo.Code.Once.Lang.Type.Sub.d_right_258 (coe v16)))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
         (coe v18))
-- Once.Adequacy.CoherenceHet._.forkc-h
d_forkc'45'h_1184 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_forkc'45'h_1184 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 ~v11 v12 v13
                  v14 v15 v16 v17 v18 v19 v20
  = du_forkc'45'h_1184
      v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_forkc'45'h_1184 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_forkc'45'h_1184 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16 v17 v18
  = case coe v17 of
      C_'8773'i_402 v21
        -> case coe v18 of
             C_'8773'i_402 v24
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                       (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                          (coe v8))
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                          (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v7) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v6) (coe v9)))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                             (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62 v15 v16)
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v3 v8 v11 v13))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v3 v8
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                v15
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v11)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                v16
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v13))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v3 v8 v12 v14)
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                          (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
                             (coe v8))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v7) (coe v10)))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v3 v8
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                   v15
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                v11)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v9))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                   v16
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                v13))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v6) (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62 v15 v16)
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v3 v8 v11 v13))
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fork'45'coerce_1906
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4) (coe v6)
                             (coe v7) (coe v9) (coe v10) (coe v5) (coe v15) (coe v16)
                             (coe MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))
                             (coe v11) (coe v13)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fork'45'cong_1110
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4) (coe v7)
                          (coe v10) (coe v5)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                v15
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v11)
                          (coe v12)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                                v16
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             v13)
                          (coe v14) (coe v21) (coe v24)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.catac-h
d_catac'45'h_1212 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384
d_catac'45'h_1212 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10 v11 v12 v13
                  v14 v15
  = du_catac'45'h_1212
      v0 v1 v2 v3 v4 v5 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_catac'45'h_1212 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384
du_catac'45'h_1212 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14
  = case coe v13 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v22 v23 v24
        -> case coe v14 of
             C_'8773'i_402 v27
               -> coe
                    C_'8773'i_402
                    (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                       (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                          (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                          (coe v6))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                             (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7)))
                             v12
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8 v10))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                             (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7)))
                             v23
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8 v10))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v9 v11)
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
                          (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                             (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                             (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v6))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7)))
                             v23
                             (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8 v10))
                       (coe
                          MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                          (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                             (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                             (coe v6))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v4))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                   (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7)))
                                v23
                                (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8 v10))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v7)
                                      (coe v4))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v4))
                                (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v22 v23 v24)
                                v10))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v9 v11)
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'sym_116
                             (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v7)
                                         (coe v4))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                      (coe v4))
                                   (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v22 v23 v24)
                                   v10))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                   (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v4))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                      (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7)))
                                   v23
                                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
                                (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8 v10))
                             (coe
                                MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_cata'45'coerce_1984
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v4) (coe v6)
                                (coe v5) (coe v8) (coe v22) (coe v23) (coe v24) (coe v10)))
                          (coe
                             MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                             (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                (coe v6))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v7)
                                         (coe v4))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                      (coe v4))
                                   (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v22 v23 v24)
                                   v10))
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8 v11)
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v9 v11)
                             (coe
                                MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_cata'45'cong_1202
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v6) (coe v5)
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v7)
                                         (coe v4))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                      (coe v4))
                                   (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v22 v23 v24)
                                   v10)
                                (coe v11) (coe v27))
                             (coe
                                MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8801''8594''8776'_176
                                (coe v0) (coe v1) (coe v2)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                   (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v7))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                                   (coe v6))
                                (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v8 v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.di-h
d_di'45'h_1246 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  T__'8773'__384 -> T__'8773'__384
d_di'45'h_1246 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
               v14 v15 v16 v17 v18 v19 v20
  = du_di'45'h_1246
      v0 v1 v2 v3 v4 v5 v6 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_di'45'h_1246 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  T__'8773'__384 -> T__'8773'__384
du_di'45'h_1246 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15
  = case coe v15 of
      C_'8773'i_402 v18
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                   (coe v6))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v11
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v6))
                      v12)
                   v9)
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v11
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v6))
                      v12)
                   v10)
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v6))
                      v14)
                   v10)
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'cong_818
                   (coe v0) (coe v1) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v11
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v6))
                      v12)
                   (coe v9) (coe v10) (coe v18))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
                   (coe v0) (coe v1) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v13
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v6))
                      v14)
                   (coe v10)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.U
d_U_1264 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 -> ()
d_U_1264 = erased
-- Once.Adequacy.CoherenceHet._.resolved-go
d_resolved'45'go_1286 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  T__'8773'__384
d_resolved'45'go_1286 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_resolved'45'go_1286 v0 v1 v2 v3 v11
du_resolved'45'go_1286 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  T__'8773'__384
du_resolved'45'go_1286 v0 v1 v2 v3 v4
  = coe
      du_'8773''45'refl_414 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
      (coe v3) (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v2 v4)
-- Once.Adequacy.CoherenceHet._.resolved-h
d_resolved'45'h_1322 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  T__'8773'__384
d_resolved'45'h_1322 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_resolved'45'h_1322 v0 v1 v2 v3 v10
du_resolved'45'h_1322 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  T__'8773'__384
du_resolved'45'h_1322 v0 v1 v2 v3 v4
  = coe
      du_resolved'45'go_1286 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.CoherenceHet._.own-go
d_own'45'go_1354 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__384
d_own'45'go_1354 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_own'45'go_1354 v0 v1 v2 v3
du_own'45'go_1354 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T__'8773'__384
du_own'45'go_1354 v0 v1 v2 v3
  = coe
      du_'8773''45'refl_414 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
      (coe v3)
      (coe
         du_RI_224 v1
         (coe
            MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
            (coe
               MAlonzo.Code.Once.Spec.Name.C_canonical_12
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
         v3
         (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
         (coe MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_78))
-- Once.Adequacy.CoherenceHet._.own-h
d_own'45'h_1374 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__384
d_own'45'h_1374 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_own'45'h_1374 v0 v1 v2 v3
du_own'45'h_1374 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T__'8773'__384
du_own'45'h_1374 v0 v1 v2 v3
  = coe du_own'45'go_1354 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.CoherenceHet._.local-go
d_local'45'go_1404 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 ->
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__384
d_local'45'go_1404 v0 v1 v2 v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_local'45'go_1404 v0 v1 v2 v3 v5 v7
du_local'45'go_1404 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 -> T__'8773'__384
du_local'45'go_1404 v0 v1 v2 v3 v4 v5
  = coe
      du_'8773''45'refl_414 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
      (coe v3)
      (coe
         du_RI_224 v1 (coe MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 (coe v2))
         v3 v4
         (coe MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v5))
-- Once.Adequacy.CoherenceHet._.local-h
d_local'45'h_1428 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 ->
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__384
d_local'45'h_1428 v0 v1 v2 v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_local'45'h_1428 v0 v1 v2 v3 v5 v7
du_local'45'h_1428 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 -> T__'8773'__384
du_local'45'h_1428 v0 v1 v2 v3 v4 v5
  = coe
      du_local'45'go_1404 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
-- Once.Adequacy.CoherenceHet._.import-go
d_import'45'go_1458 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__384
d_import'45'go_1458 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                    ~v12 ~v13
  = du_import'45'go_1458 v0 v1 v2 v3 v9
du_import'45'go_1458 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  T__'8773'__384
du_import'45'go_1458 v0 v1 v2 v3 v4
  = coe
      du_'8773''45'refl_414 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
      (coe v3)
      (coe
         du_RI_224 v1 (coe MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 (coe v2))
         v3
         (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
         (coe MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_86 v4))
-- Once.Adequacy.CoherenceHet._.import-h
d_import'45'h_1486 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__384
d_import'45'h_1486 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                   ~v12
  = du_import'45'h_1486 v0 v1 v2 v3 v9
du_import'45'h_1486 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  T__'8773'__384
du_import'45'h_1486 v0 v1 v2 v3 v4
  = coe
      du_import'45'go_1458 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.CoherenceHet._.poly-ty
d_poly'45'ty_1510 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__384
d_poly'45'ty_1510 v0 v1 v2 v3 ~v4 ~v5
  = du_poly'45'ty_1510 v0 v1 v2 v3
du_poly'45'ty_1510 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T__'8773'__384
du_poly'45'ty_1510 v0 v1 v2 v3
  = coe
      du_'8773''45'refl_414 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
      (coe v3) (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2)
-- Once.Adequacy.CoherenceHet._.polyinf-go
d_polyinf'45'go_1540 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__384
d_polyinf'45'go_1540 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                     ~v12 ~v13 ~v14 ~v15
  = du_polyinf'45'go_1540 v0 v1 v2 v3
du_polyinf'45'go_1540 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T__'8773'__384
du_polyinf'45'go_1540 v0 v1 v2 v3
  = coe du_poly'45'ty_1510 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.CoherenceHet._.polyinf-h
d_polyinf'45'h_1594 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__384
d_polyinf'45'h_1594 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                    ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
  = du_polyinf'45'h_1594 v0 v1 v2 v3
du_polyinf'45'h_1594 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T__'8773'__384
du_polyinf'45'h_1594 v0 v1 v2 v3
  = coe du_polyinf'45'go_1540 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.CoherenceHet._.arith-h
d_arith'45'h_1626 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_arith'45'h_1626 v0 v1 v2 v3 v4 ~v5 ~v6 v7 ~v8 v9 ~v10 v11 v12 v13
                  v14 v15 v16
  = du_arith'45'h_1626 v0 v1 v2 v3 v4 v7 v9 v11 v12 v13 v14 v15 v16
du_arith'45'h_1626 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_arith'45'h_1626 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_add'45'cong_200
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_sub'45'cong_238
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_mul'45'cong_276
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_div'45'cong_314
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpMod_16
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_mod'45'cong_352
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.farith-h
d_farith'45'h_1670 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_farith'45'h_1670 v0 v1 v2 v3 v4 ~v5 ~v6 v7 ~v8 v9 ~v10 v11 v12
                   v13 v14 v15 v16
  = du_farith'45'h_1670 v0 v1 v2 v3 v4 v7 v9 v11 v12 v13 v14 v15 v16
du_farith'45'h_1670 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_farith'45'h_1670 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fadd'45'cong_390
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fsub'45'cong_428
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fmul'45'cong_466
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fdiv'45'cong_504
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.il-h
d_il'45'h_1710 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_il'45'h_1710 v0 v1 v2 v3 v4 ~v5 ~v6 v7 ~v8 v9 ~v10 v11 v12 v13
               v14 v15 v16
  = du_il'45'h_1710 v0 v1 v2 v3 v4 v7 v9 v11 v12 v13 v14 v15 v16
du_il'45'h_1710 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_il'45'h_1710 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fadd'45'cong_390
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v7)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v8)))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v10))
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_i2f'45'cong_788
                                 (coe v0)
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v8))
                                 (coe v15))
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fsub'45'cong_428
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v7)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v8)))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v10))
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_i2f'45'cong_788
                                 (coe v0)
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v8))
                                 (coe v15))
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fmul'45'cong_466
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v7)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v8)))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v10))
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_i2f'45'cong_788
                                 (coe v0)
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v8))
                                 (coe v15))
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fdiv'45'cong_504
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v7)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v8)))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v6)
                                 (coe v10))
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_i2f'45'cong_788
                                 (coe v0)
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v5) (coe v8))
                                 (coe v15))
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.ir-h
d_ir'45'h_1750 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_ir'45'h_1750 v0 v1 v2 v3 v4 ~v5 ~v6 v7 ~v8 v9 ~v10 v11 v12 v13
               v14 v15 v16
  = du_ir'45'h_1750 v0 v1 v2 v3 v4 v7 v9 v11 v12 v13 v14 v15 v16
du_ir'45'h_1750 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_ir'45'h_1750 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fadd'45'cong_390
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v9)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v10)))
                              (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_i2f'45'cong_788
                                 (coe v0)
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v9))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v10))
                                 (coe v18)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fsub'45'cong_428
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v9)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v10)))
                              (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_i2f'45'cong_788
                                 (coe v0)
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v9))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v10))
                                 (coe v18)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fmul'45'cong_466
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v9)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v10)))
                              (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_i2f'45'cong_788
                                 (coe v0)
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v9))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v10))
                                 (coe v18)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_fdiv'45'cong_504
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v9)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                 (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v10)))
                              (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_i2f'45'cong_788
                                 (coe v0)
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v9))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                    (coe v1) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                    (coe v6) (coe v10))
                                 (coe v18)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.cmp-h
d_cmp'45'h_1790 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
d_cmp'45'h_1790 v0 v1 v2 v3 v4 ~v5 ~v6 v7 ~v8 v9 ~v10 v11 v12 v13
                v14 v15 v16
  = du_cmp'45'h_1790 v0 v1 v2 v3 v4 v7 v9 v11 v12 v13 v14 v15 v16
du_cmp'45'h_1790 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384 -> T__'8773'__384
du_cmp'45'h_1790 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Syntax.C_OpLt_18
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_lt'45'cong_542
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpLe_20
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_le'45'cong_580
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpGt_22
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_gt'45'cong_618
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpGe_24
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_ge'45'cong_656
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpEq_26
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_eq'45'cong_694
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Syntax.C_OpNe_28
        -> case coe v11 of
             C_'8773'i_402 v15
               -> case coe v12 of
                    C_'8773'i_402 v18
                      -> coe
                           C_'8773'i_402
                           (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_ne'45'cong_732
                              (coe v0)
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                              (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v5)
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                                 (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6)
                                 (coe v10))
                              (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.idapp-h
d_idapp'45'h_1828 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
d_idapp'45'h_1828 v0 v1 v2 v3 ~v4 v5 ~v6 v7 v8 v9
  = du_idapp'45'h_1828 v0 v1 v2 v3 v5 v7 v8 v9
du_idapp'45'h_1828 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
du_idapp'45'h_1828 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_'8773'i_402 v10
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe v4) (coe v3) (coe v3) (coe MAlonzo.Code.Once.IR.C_id_20)
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2) (coe v3) (coe v4) (coe v5))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2) (coe v3) (coe v4) (coe v6))
                (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.fstapp-h
d_fstapp'45'h_1848 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
d_fstapp'45'h_1848 v0 v1 v2 v3 ~v4 v5 ~v6 v7 ~v8 v9 v10 v11
  = du_fstapp'45'h_1848 v0 v1 v2 v3 v5 v7 v9 v10 v11
du_fstapp'45'h_1848 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
du_fstapp'45'h_1848 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_'8773'i_402 v11
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe v5)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                (coe v3) (coe MAlonzo.Code.Once.IR.C_fst_42)
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2)
                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                   (coe v5) (coe v6))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2)
                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                   (coe v5) (coe v7))
                (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.sndapp-h
d_sndapp'45'h_1868 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
d_sndapp'45'h_1868 v0 v1 v2 v3 ~v4 v5 ~v6 v7 ~v8 v9 v10 v11
  = du_sndapp'45'h_1868 v0 v1 v2 v3 v5 v7 v9 v10 v11
du_sndapp'45'h_1868 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
du_sndapp'45'h_1868 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_'8773'i_402 v11
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe v5)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                (coe v4) (coe MAlonzo.Code.Once.IR.C_snd_48)
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2)
                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                   (coe v5) (coe v6))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2)
                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                   (coe v5) (coe v7))
                (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.termapp-h
d_termapp'45'h_1884 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
d_termapp'45'h_1884 v0 v1 v2 v3 ~v4 v5 ~v6 v7 v8 v9
  = du_termapp'45'h_1884 v0 v1 v2 v3 v5 v7 v8 v9
du_termapp'45'h_1884 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
du_termapp'45'h_1884 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_'8773'i_402 v10
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe v4) (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                (coe MAlonzo.Code.Once.IR.C_terminal_72)
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2) (coe v3) (coe v4) (coe v5))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2) (coe v3) (coe v4) (coe v6))
                (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.apply-h
d_apply'45'h_1904 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
d_apply'45'h_1904 v0 v1 v2 v3 ~v4 v5 ~v6 v7 ~v8 v9 v10 v11
  = du_apply'45'h_1904 v0 v1 v2 v3 v5 v7 v9 v10 v11
du_apply'45'h_1904 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
du_apply'45'h_1904 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_'8773'i_402 v11
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'42'__24
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                      (coe v4))
                   (coe v3))
                (coe v4) (coe MAlonzo.Code.Once.IR.C_apply_90)
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                         (coe v4))
                      (coe v3))
                   (coe v5) (coe v6))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                         (coe v4))
                      (coe v3))
                   (coe v5) (coe v7))
                (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.applyeff-h
d_applyeff'45'h_1932 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_56 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_56 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
d_applyeff'45'h_1932 v0 v1 v2 v3 ~v4 v5 ~v6 v7 ~v8 v9 ~v10 ~v11
                     ~v12 v13 v14 v15
  = du_applyeff'45'h_1932 v0 v1 v2 v3 v5 v7 v9 v13 v14 v15
du_applyeff'45'h_1932 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
du_applyeff'45'h_1932 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_'8773'i_402 v12
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'42'__24
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
                      (coe v4))
                   (coe v3))
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
                   (coe v4))
                (coe
                   MAlonzo.Code.Once.IR.C_curry_84
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__28
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe
                            MAlonzo.Code.Once.IRTy.C__'8667'__24
                            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4)))
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
                      (coe MAlonzo.Code.Once.IR.C_apply_90)
                      (coe MAlonzo.Code.Once.IR.C_fst_42)))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
                         (coe v4))
                      (coe v3))
                   (coe v5) (coe v7))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
                         (coe v4))
                      (coe v3))
                   (coe v5) (coe v8))
                (coe v12))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.out-h
d_out'45'h_1952 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
d_out'45'h_1952 v0 v1 v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_out'45'h_1952 v0 v1 v2 v3 v5 v7 v8 v9 v10 v11
du_out'45'h_1952 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
du_out'45'h_1952 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_'8773'i_402 v12
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                   (coe
                      MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4)))
                (coe
                   MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42)))
                (coe
                   du_RI_224 v1
                   (coe
                      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                         (coe
                            MAlonzo.Code.Once.Spec.Name.C_canonical_12
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe ("Generators" :: Data.Text.Text))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("Out" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe v2))
                   (MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42)))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe
                         MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4)))
                   (coe
                      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_356 v3 v4
                      v5 v7))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v4
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                   (coe
                      MAlonzo.Code.Once.IR.C_Out_110
                      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                         (coe v3) (coe v5)))
                   (coe
                      du_RI_224 v1 v2
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                      v4 v8))
                (coe
                   du_RI_224 v1
                   (coe
                      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                         (coe
                            MAlonzo.Code.Once.Spec.Name.C_canonical_12
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe ("Generators" :: Data.Text.Text))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("Out" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe v2))
                   (MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42)))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe
                         MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4)))
                   (coe
                      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_356 v3 v4
                      v6 v8))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                   (coe v0)
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                   (coe v4)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42)))
                   (coe
                      MAlonzo.Code.Once.IR.C_Out_110
                      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                         (coe v3) (coe v5)))
                   (coe
                      MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                      (coe v2)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                      (coe v4) (coe v7))
                   (coe
                      du_RI_224 v1 v2
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                      v4 v8)
                   (coe v12))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8801''8594''8776'_176
                   (coe v0)
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42)))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v4
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                      (coe
                         MAlonzo.Code.Once.IR.C_Out_110
                         (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                            (coe v3) (coe v5)))
                      (coe
                         du_RI_224 v1 v2
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                         v4 v8))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.outeff-h
d_outeff'45'h_1980 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
d_outeff'45'h_1980 v0 v1 v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_outeff'45'h_1980 v0 v1 v2 v3 v5 v7 v8 v9 v10 v11
du_outeff'45'h_1980 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
du_outeff'45'h_1980 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_'8773'i_402 v12
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                   (coe
                      MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4)))
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))))
                (coe
                   du_RI_224 v1
                   (coe
                      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                         (coe
                            MAlonzo.Code.Once.Spec.Name.C_canonical_12
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe ("Generators" :: Data.Text.Text))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("Out" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe v2))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe
                         MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4)))
                   (coe
                      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_368
                      v3 v4 v5 v7))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v4
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                   (coe
                      MAlonzo.Code.Once.IR.C_curry_84
                      (coe
                         MAlonzo.Code.Once.IR.C__'8728'__28
                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44)))
                         (coe
                            MAlonzo.Code.Once.IR.C_Out_110
                            (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                               (coe v3) (coe v5)))
                         (coe MAlonzo.Code.Once.IR.C_fst_42)))
                   (coe
                      du_RI_224 v1 v2
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                      v4 v8))
                (coe
                   du_RI_224 v1
                   (coe
                      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                         (coe
                            MAlonzo.Code.Once.Spec.Name.C_canonical_12
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe ("Generators" :: Data.Text.Text))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("Out" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe v2))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe
                         MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4)))
                   (coe
                      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_368
                      v3 v4 v6 v8))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                   (coe v0)
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                   (coe v4)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))))
                   (coe
                      MAlonzo.Code.Once.IR.C_curry_84
                      (coe
                         MAlonzo.Code.Once.IR.C__'8728'__28
                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44)))
                         (coe
                            MAlonzo.Code.Once.IR.C_Out_110
                            (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                               (coe v3) (coe v5)))
                         (coe MAlonzo.Code.Once.IR.C_fst_42)))
                   (coe
                      MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                      (coe v2)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                      (coe v4) (coe v7))
                   (coe
                      du_RI_224 v1 v2
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                      v4 v8)
                   (coe v12))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8801''8594''8776'_176
                   (coe v0)
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v4
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                      (coe
                         MAlonzo.Code.Once.IR.C_curry_84
                         (coe
                            MAlonzo.Code.Once.IR.C__'8728'__28
                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44)))
                            (coe
                               MAlonzo.Code.Once.IR.C_Out_110
                               (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                  (coe v3) (coe v5)))
                            (coe MAlonzo.Code.Once.IR.C_fst_42)))
                      (coe
                         du_RI_224 v1 v2
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v3)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                         v4 v8))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.applychk-h
d_applychk'45'h_2006 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
d_applychk'45'h_2006 v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 v9 v10
  = du_applychk'45'h_2006 v0 v1 v2 v3 v5 v6 v8 v9 v10
du_applychk'45'h_2006 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__384 -> T__'8773'__384
du_applychk'45'h_2006 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_'8773'i_402 v11
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'42'__24
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                      (coe v4))
                   (coe v3))
                (coe v4) (coe MAlonzo.Code.Once.IR.C_apply_90)
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                         (coe v4))
                      (coe v3))
                   (coe v5) (coe v6))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                   (coe v2)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                         (coe v4))
                      (coe v3))
                   (coe v5) (coe v7))
                (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.applyic-h
d_applyic'45'h_2030 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8773'__384 -> T__'8773'__384
d_applyic'45'h_2030 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 ~v9 v10 v11 v12
                    ~v13 v14
  = du_applyic'45'h_2030 v0 v1 v2 v3 v5 v8 v10 v11 v12 v14
du_applyic'45'h_2030 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  T__'8773'__384 -> T__'8773'__384
du_applyic'45'h_2030 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_'8773'i_402 v12
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                   (coe
                      MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5)))
                (coe v4)
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4 v8
                   (coe
                      du_RI_224 v1
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                         (coe
                            MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                            (coe
                               MAlonzo.Code.Once.Spec.Name.C_canonical_12
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("Generators" :: Data.Text.Text))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("apply" :: Data.Text.Text))
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                         (coe v2))
                      v4
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                         (coe
                            MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5)))
                      (coe
                         MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_328 v3
                         v5 v6)))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4
                   (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                   (coe
                      du_RI_224 v1
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                         (coe
                            MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                            (coe
                               MAlonzo.Code.Once.Spec.Name.C_canonical_12
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("Generators" :: Data.Text.Text))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("apply" :: Data.Text.Text))
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                         (coe v2))
                      v4
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                         (coe
                            MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5)))
                      (coe
                         MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_328 v3
                         v5 v6)))
                (coe
                   du_RC_226 v1
                   (coe
                      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                         (coe
                            MAlonzo.Code.Once.Spec.Name.C_canonical_12
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe ("Generators" :: Data.Text.Text))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("apply" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe v2))
                   v4
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe
                         MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5)))
                   (coe
                      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_724 v3 v5 v7))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
                   (coe v0)
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                   (coe v4) (coe v4)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                   (coe
                      du_RI_224 v1
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                         (coe
                            MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                            (coe
                               MAlonzo.Code.Once.Spec.Name.C_canonical_12
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("Generators" :: Data.Text.Text))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("apply" :: Data.Text.Text))
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                         (coe v2))
                      v4
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                         (coe
                            MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5)))
                      (coe
                         MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_328 v3
                         v5 v6)))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                   (coe v0)
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe
                         MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5)))
                   (coe v4)
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4
                      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                      (coe
                         du_RI_224 v1
                         (coe
                            MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                            (coe
                               MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                               (coe
                                  MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("Generators" :: Data.Text.Text))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe ("apply" :: Data.Text.Text))
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                            (coe v2))
                         v4
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                            (coe
                               MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                               (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5)))
                         (coe
                            MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_328 v3
                            v5 v6)))
                   (coe
                      du_RI_224 v1
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                         (coe
                            MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                            (coe
                               MAlonzo.Code.Once.Spec.Name.C_canonical_12
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("Generators" :: Data.Text.Text))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("apply" :: Data.Text.Text))
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                         (coe v2))
                      v4
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                         (coe
                            MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5)))
                      (coe
                         MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_328 v3
                         v5 v6))
                   (coe
                      du_RC_226 v1
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                         (coe
                            MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                            (coe
                               MAlonzo.Code.Once.Spec.Name.C_canonical_12
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("Generators" :: Data.Text.Text))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("apply" :: Data.Text.Text))
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                         (coe v2))
                      v4
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                         (coe
                            MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5)))
                      (coe
                         MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_724 v3 v5 v7))
                   (coe
                      MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'refl_1472
                      (coe v0)
                      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                      (coe v4)
                      (coe
                         du_RI_224 v1
                         (coe
                            MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                            (coe
                               MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                               (coe
                                  MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("Generators" :: Data.Text.Text))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe ("apply" :: Data.Text.Text))
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                            (coe v2))
                         v4
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                            (coe
                               MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                               (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5)))
                         (coe
                            MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_328 v3
                            v5 v6)))
                   (coe
                      MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                      (coe v0)
                      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                      (coe v5)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'42'__24
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                            (coe v4))
                         (coe v3))
                      (coe v4) (coe MAlonzo.Code.Once.IR.C_apply_90)
                      (coe
                         MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                         (coe v2)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C__'42'__24
                            (coe
                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                               (coe v4))
                            (coe v3))
                         (coe v5) (coe v6))
                      (coe
                         MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30 (coe v1)
                         (coe v2)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C__'42'__24
                            (coe
                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                               (coe v4))
                            (coe v3))
                         (coe v5) (coe v7))
                      (coe v12))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.In-h
d_In'45'h_2050 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__384 -> T__'8773'__384
d_In'45'h_2050 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9 v10
  = du_In'45'h_2050 v0 v1 v2 v3 v4 v6 v7 v8 v9 v10
du_In'45'h_2050 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__384 -> T__'8773'__384
du_In'45'h_2050 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_'8773'i_402 v12
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                   (coe
                      MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4)))
                (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3))
                (coe
                   du_RC_226 v1
                   (coe
                      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                         (coe
                            MAlonzo.Code.Once.Spec.Name.C_canonical_12
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe ("Generators" :: Data.Text.Text))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("In" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe v2))
                   (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe
                         MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4)))
                   (coe
                      MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_712 v4 v5
                      v7))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v4
                   (MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                      (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3)))
                   (coe
                      MAlonzo.Code.Once.IR.C_In_94
                      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                         (coe v3) (coe v5)))
                   (coe
                      du_RC_226 v1 v2
                      (MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                         (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3)))
                      v4 v8))
                (coe
                   du_RC_226 v1
                   (coe
                      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                      (coe
                         MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40
                         (coe
                            MAlonzo.Code.Once.Spec.Name.C_canonical_12
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe ("Generators" :: Data.Text.Text))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe ("In" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe v2))
                   (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe
                         MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4)))
                   (coe
                      MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_712 v4 v6
                      v8))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                   (coe v0)
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                   (coe v4)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                      (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3)))
                   (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3))
                   (coe
                      MAlonzo.Code.Once.IR.C_In_94
                      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                         (coe v3) (coe v5)))
                   (coe
                      MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v1) (coe v2)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                         (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3)))
                      (coe v4) (coe v7))
                   (coe
                      du_RC_226 v1 v2
                      (MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                         (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3)))
                      v4 v8)
                   (coe v12))
                (coe
                   MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_'8801''8594''8776'_176
                   (coe v0)
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                   (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v4
                      (MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                         (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3)))
                      (coe
                         MAlonzo.Code.Once.IR.C_In_94
                         (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                            (coe v3) (coe v5)))
                      (coe
                         du_RC_226 v1 v2
                         (MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                            (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v3)))
                         v4 v8))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.inlapp-h
d_inlapp'45'h_2074 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__384 -> T__'8773'__384
d_inlapp'45'h_2074 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 v9
  = du_inlapp'45'h_2074 v0 v1 v2 v3 v4 v5 v7 v8 v9
du_inlapp'45'h_2074 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__384 -> T__'8773'__384
du_inlapp'45'h_2074 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_'8773'i_402 v11
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe v5) (coe v3)
                (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v3) (coe v4))
                (coe MAlonzo.Code.Once.IR.C_inl_54)
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v1) (coe v2)
                   (coe v3) (coe v5) (coe v6))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v1) (coe v2)
                   (coe v3) (coe v5) (coe v7))
                (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.inrapp-h
d_inrapp'45'h_2090 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__384 -> T__'8773'__384
d_inrapp'45'h_2090 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 v9
  = du_inrapp'45'h_2090 v0 v1 v2 v3 v4 v5 v7 v8 v9
du_inrapp'45'h_2090 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__384 -> T__'8773'__384
du_inrapp'45'h_2090 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_'8773'i_402 v11
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe v5) (coe v4)
                (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v3) (coe v4))
                (coe MAlonzo.Code.Once.IR.C_inr_60)
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v1) (coe v2)
                   (coe v4) (coe v5) (coe v6))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v1) (coe v2)
                   (coe v4) (coe v5) (coe v7))
                (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.initapp-h
d_initapp'45'h_2104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__384 -> T__'8773'__384
d_initapp'45'h_2104 v0 v1 v2 v3 v4 ~v5 v6 v7 v8
  = du_initapp'45'h_2104 v0 v1 v2 v3 v4 v6 v7 v8
du_initapp'45'h_2104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__384 -> T__'8773'__384
du_initapp'45'h_2104 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_'8773'i_402 v10
        -> coe
             C_'8773'i_402
             (MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.d_morph'45'app'45'cong_854
                (coe v0)
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
                (coe v4) (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v3)
                (coe MAlonzo.Code.Once.IR.C_initial_76)
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v4) (coe v5))
                (coe
                   MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v4) (coe v6))
                (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceHet._.polydc-go
d_polydc'45'go_2128 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 -> T__'8773'__384
d_polydc'45'go_2128 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 v10 v11
  = du_polydc'45'go_2128 v0 v1 v2 v3 v4 v6 v10 v11
du_polydc'45'go_2128 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 -> T__'8773'__384
du_polydc'45'go_2128 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_'8773'i_402
      (MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
         (coe v0)
         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
         (coe
            MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v4))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
               (coe v4))
            (coe
               MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
               (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3)) v7
               (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                  (coe v4))
               (coe
                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                  (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3))
                  (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                  v6)
               (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
               (coe v4))
            (MAlonzo.Code.Once.Lang.Laws.SubLaws.d_'60''58''45'trans_86
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                  (coe v4))
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                  (coe v4))
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                  (coe v4))
               (coe
                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                  (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3))
                  (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                  v6)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                  (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3)) v7
                  (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))))
            (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2))
         (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2)
         (coe
            MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'trans_1502
            (coe v0)
            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
               (coe v4))
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
               (coe v4))
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
               (coe v4))
            (coe
               MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
               (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3))
               (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
               v6)
            (coe
               MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
               (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3)) v7
               (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5)))
            (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2))
         (coe
            MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'trans_146
            (coe v0)
            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
            (coe
               MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
               (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1)))
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
               (coe v4))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                  (coe v4))
               (MAlonzo.Code.Once.Lang.Laws.SubLaws.d_'60''58''45'trans_86
                  (coe
                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                     (coe v4))
                  (coe
                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                     (coe v4))
                  (coe
                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                     (coe v4))
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                     (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3))
                     (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
                     v6)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                     (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3)) v7
                     (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94 (coe v5))))
               (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                  (coe v4))
               (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                  (coe
                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                     (coe v4)))
               (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2))
            (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2)
            (coe
               MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
               (coe v0)
               (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
               (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                  (coe v4))
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                  (coe v4))
               (coe
                  MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                  (coe
                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                     (coe v4)))
               (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2))
            (coe
               MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'refl_1472
               (coe v0)
               (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
               (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                  (coe v4))
               (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2))))
-- Once.Adequacy.CoherenceHet._.polydd-go
d_polydd'45'go_2156 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> T__'8773'__384
d_polydd'45'go_2156 v0 v1 v2 v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_polydd'45'go_2156 v0 v1 v2 v3 v4 v6 v7 v12
du_polydd'45'go_2156 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> T__'8773'__384
du_polydd'45'go_2156 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_'8773'i_402
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap.du_coerce'45'uniq_1538
         (coe v0)
         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v1))
         (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v1))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
            (coe v4))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v4))
         (coe
            MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v3))
            (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v4))
            v7)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v2))
-- Once.Adequacy.CoherenceHet._.polydc-h
d_polydc'45'h_2208 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 -> T__'8773'__384
d_polydc'45'h_2208 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
                   ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 v24
  = du_polydc'45'h_2208 v0 v1 v2 v3 v4 v6 v23 v24
du_polydc'45'h_2208 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 -> T__'8773'__384
du_polydc'45'h_2208 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_polydc'45'go_2128 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7)
-- Once.Adequacy.CoherenceHet._.polydd-h
d_polydd'45'h_2280 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> T__'8773'__384
d_polydd'45'h_2280 v0 v1 v2 v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
                   ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                   ~v26 ~v27 v28
  = du_polydd'45'h_2280 v0 v1 v2 v3 v4 v6 v7 v28
du_polydd'45'h_2280 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> T__'8773'__384
du_polydd'45'h_2280 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_polydd'45'go_2156 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7)
