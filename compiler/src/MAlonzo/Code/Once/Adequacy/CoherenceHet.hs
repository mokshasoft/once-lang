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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Adequacy.CoherenceLaws
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Lang.Context
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
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'out_132 = erased
-- Once.Adequacy.CoherenceHet.RI
d_RI_222 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_RI_222 ~v0 = du_RI_222
du_RI_222 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_RI_222
  = coe MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
-- Once.Adequacy.CoherenceHet.RC
d_RC_224 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_RC_224 ~v0 = du_RC_224
du_RC_224 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_RC_224 = coe MAlonzo.Code.Once.Denotation.Realize.d_realize_20
-- Once.Adequacy.CoherenceHet.uip
d_uip_240 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uip_240 = erased
-- Once.Adequacy.CoherenceHet.as-grade
d_as'45'grade_282 ::
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
d_as'45'grade_282 = erased
-- Once.Adequacy.CoherenceHet.cod-≡
d_cod'45''8801'_296 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cod'45''8801'_296 = erased
-- Once.Adequacy.CoherenceHet.Same2
d_Same2_362 ::
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
d_Same2_362 = erased
-- Once.Adequacy.CoherenceHet._≅_
d__'8773'__382 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T__'8773'__382 = C_'8773'i_400
-- Once.Adequacy.CoherenceHet._≅_.≅-ty
d_'8773''45'ty_394 ::
  T__'8773'__382 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8773''45'ty_394 = erased
-- Once.Adequacy.CoherenceHet._≅_.≅-us
d_'8773''45'us_396 ::
  T__'8773'__382 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8773''45'us_396 = erased
-- Once.Adequacy.CoherenceHet._≅_.≅-sem
d_'8773''45'sem_398 :: T__'8773'__382 -> AgdaAny
d_'8773''45'sem_398 = erased
-- Once.Adequacy.CoherenceHet.≅-of
d_'8773''45'of_406 ::
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__34 ->
  T__'8773'__382
d_'8773''45'of_406 = erased
-- Once.Adequacy.CoherenceHet.≅-refl
d_'8773''45'refl_412 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> T__'8773'__382
d_'8773''45'refl_412 = erased
-- Once.Adequacy.CoherenceHet.≅-sym
d_'8773''45'sym_418 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__382 -> T__'8773'__382
d_'8773''45'sym_418 = erased
-- Once.Adequacy.CoherenceHet.≅-≈
d_'8773''45''8776'_426 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__382 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__34
d_'8773''45''8776'_426 = erased
-- Once.Adequacy.CoherenceHet._.pair-h
d_pair'45'h_446 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_pair'45'h_446 = erased
-- Once.Adequacy.CoherenceHet._.neg-h
d_neg'45'h_456 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__382 -> T__'8773'__382
d_neg'45'h_456 = erased
-- Once.Adequacy.CoherenceHet._.let-h
d_let'45'h_468 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_let'45'h_468 = erased
-- Once.Adequacy.CoherenceHet._.case-h
d_case'45'h_506 ::
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
  T__'8773'__382 ->
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_case'45'h_506 = erased
-- Once.Adequacy.CoherenceHet._.app-h
d_app'45'h_522 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_app'45'h_522 = erased
-- Once.Adequacy.CoherenceHet._.effApp-h
d_effApp'45'h_540 ::
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
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_effApp'45'h_540 = erased
-- Once.Adequacy.CoherenceHet._.comp-h
d_comp'45'h_554 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_comp'45'h_554 = erased
-- Once.Adequacy.CoherenceHet._.copair-h
d_copair'45'h_568 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_copair'45'h_568 = erased
-- Once.Adequacy.CoherenceHet._.fork-h
d_fork'45'h_582 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_fork'45'h_582 = erased
-- Once.Adequacy.CoherenceHet._.curry-h
d_curry'45'h_592 ::
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
  T__'8773'__382 -> T__'8773'__382
d_curry'45'h_592 = erased
-- Once.Adequacy.CoherenceHet._.coerce-h
d_coerce'45'h_604 ::
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
  T__'8773'__382 -> T__'8773'__382
d_coerce'45'h_604 = erased
-- Once.Adequacy.CoherenceHet._.lam-h
d_lam'45'h_620 ::
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
  T__'8773'__382 -> T__'8773'__382
d_lam'45'h_620 = erased
-- Once.Adequacy.CoherenceHet._.lamd-h
d_lamd'45'h_644 ::
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
  T__'8773'__382 -> T__'8773'__382
d_lamd'45'h_644 = erased
-- Once.Adequacy.CoherenceHet._.cata-h
d_cata'45'h_662 ::
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
  T__'8773'__382 -> T__'8773'__382
d_cata'45'h_662 = erased
-- Once.Adequacy.CoherenceHet._.ana-h
d_ana'45'h_684 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  T__'8773'__382 -> T__'8773'__382
d_ana'45'h_684 = erased
-- Once.Adequacy.CoherenceHet._.catad
d_catad_708 ::
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
  T__'8773'__382 -> T__'8773'__382
d_catad_708 = erased
-- Once.Adequacy.CoherenceHet._.catad-h
d_catad'45'h_726 ::
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
  T__'8773'__382 -> T__'8773'__382
d_catad'45'h_726 = erased
-- Once.Adequacy.CoherenceHet._.spine-h
d_spine'45'h_752 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_spine'45'h_752 = erased
-- Once.Adequacy.CoherenceHet._.gf-h
d_gf'45'h_778 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_gf'45'h_778 = erased
-- Once.Adequacy.CoherenceHet._.pairc-h
d_pairc'45'h_812 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_pairc'45'h_812 = erased
-- Once.Adequacy.CoherenceHet._.twice-h
d_twice'45'h_836 ::
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
  T__'8773'__382 -> T__'8773'__382
d_twice'45'h_836 = erased
-- Once.Adequacy.CoherenceHet._.dcsub-h
d_dcsub'45'h_860 ::
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
  T__'8773'__382 -> T__'8773'__382
d_dcsub'45'h_860 = erased
-- Once.Adequacy.CoherenceHet._.lamc-h
d_lamc'45'h_884 ::
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
  T__'8773'__382 -> T__'8773'__382
d_lamc'45'h_884 = erased
-- Once.Adequacy.CoherenceHet._.cg-h
d_cg'45'h_912 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_cg'45'h_912 = erased
-- Once.Adequacy.CoherenceHet._.cf-h
d_cf'45'h_940 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_cf'45'h_940 = erased
-- Once.Adequacy.CoherenceHet._.casec-h
d_casec'45'h_970 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_casec'45'h_970 = erased
-- Once.Adequacy.CoherenceHet._.forkc-h
d_forkc'45'h_994 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_forkc'45'h_994 = erased
-- Once.Adequacy.CoherenceHet._.catac-h
d_catac'45'h_1022 ::
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
  T__'8773'__382 -> T__'8773'__382
d_catac'45'h_1022 = erased
-- Once.Adequacy.CoherenceHet._.di-h
d_di'45'h_1056 ::
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
  T__'8773'__382 -> T__'8773'__382
d_di'45'h_1056 = erased
-- Once.Adequacy.CoherenceHet._.U
d_U_1074 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 -> ()
d_U_1074 = erased
-- Once.Adequacy.CoherenceHet._.resolved-go
d_resolved'45'go_1096 ::
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
  T__'8773'__382
d_resolved'45'go_1096 = erased
-- Once.Adequacy.CoherenceHet._.resolved-h
d_resolved'45'h_1132 ::
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
  T__'8773'__382
d_resolved'45'h_1132 = erased
-- Once.Adequacy.CoherenceHet._.own-go
d_own'45'go_1168 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__382
d_own'45'go_1168 = erased
-- Once.Adequacy.CoherenceHet._.own-h
d_own'45'h_1192 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__382
d_own'45'h_1192 = erased
-- Once.Adequacy.CoherenceHet._.qualified-go
d_qualified'45'go_1224 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  T__'8773'__382
d_qualified'45'go_1224 = erased
-- Once.Adequacy.CoherenceHet._.qualified-h
d_qualified'45'h_1254 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  T__'8773'__382
d_qualified'45'h_1254 = erased
-- Once.Adequacy.CoherenceHet._.local-go
d_local'45'go_1288 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__382
d_local'45'go_1288 = erased
-- Once.Adequacy.CoherenceHet._.local-h
d_local'45'h_1312 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__382
d_local'45'h_1312 = erased
-- Once.Adequacy.CoherenceHet._.import-go
d_import'45'go_1342 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__382
d_import'45'go_1342 = erased
-- Once.Adequacy.CoherenceHet._.import-h
d_import'45'h_1370 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__382
d_import'45'h_1370 = erased
-- Once.Adequacy.CoherenceHet._.poly-ty
d_poly'45'ty_1394 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__382
d_poly'45'ty_1394 = erased
-- Once.Adequacy.CoherenceHet._.polyinf-go
d_polyinf'45'go_1424 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__382
d_polyinf'45'go_1424 = erased
-- Once.Adequacy.CoherenceHet._.polyinf-h
d_polyinf'45'h_1478 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__382
d_polyinf'45'h_1478 = erased
-- Once.Adequacy.CoherenceHet._.arith-h
d_arith'45'h_1510 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_arith'45'h_1510 = erased
-- Once.Adequacy.CoherenceHet._.farith-h
d_farith'45'h_1554 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_farith'45'h_1554 = erased
-- Once.Adequacy.CoherenceHet._.il-h
d_il'45'h_1594 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_il'45'h_1594 = erased
-- Once.Adequacy.CoherenceHet._.ir-h
d_ir'45'h_1634 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_ir'45'h_1634 = erased
-- Once.Adequacy.CoherenceHet._.cmp-h
d_cmp'45'h_1674 ::
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
  T__'8773'__382 -> T__'8773'__382 -> T__'8773'__382
d_cmp'45'h_1674 = erased
-- Once.Adequacy.CoherenceHet._.idapp-h
d_idapp'45'h_1712 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__382 -> T__'8773'__382
d_idapp'45'h_1712 = erased
-- Once.Adequacy.CoherenceHet._.fstapp-h
d_fstapp'45'h_1732 ::
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
  T__'8773'__382 -> T__'8773'__382
d_fstapp'45'h_1732 = erased
-- Once.Adequacy.CoherenceHet._.sndapp-h
d_sndapp'45'h_1752 ::
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
  T__'8773'__382 -> T__'8773'__382
d_sndapp'45'h_1752 = erased
-- Once.Adequacy.CoherenceHet._.termapp-h
d_termapp'45'h_1768 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__382 -> T__'8773'__382
d_termapp'45'h_1768 = erased
-- Once.Adequacy.CoherenceHet._.apply-h
d_apply'45'h_1788 ::
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
  T__'8773'__382 -> T__'8773'__382
d_apply'45'h_1788 = erased
-- Once.Adequacy.CoherenceHet._.applyeff-h
d_applyeff'45'h_1816 ::
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
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__382 -> T__'8773'__382
d_applyeff'45'h_1816 = erased
-- Once.Adequacy.CoherenceHet._.out-h
d_out'45'h_1836 ::
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
  T__'8773'__382 -> T__'8773'__382
d_out'45'h_1836 = erased
-- Once.Adequacy.CoherenceHet._.outeff-h
d_outeff'45'h_1872 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  T__'8773'__382 -> T__'8773'__382
d_outeff'45'h_1872 = erased
-- Once.Adequacy.CoherenceHet._.applychk-h
d_applychk'45'h_1900 ::
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
  T__'8773'__382 -> T__'8773'__382
d_applychk'45'h_1900 = erased
-- Once.Adequacy.CoherenceHet._.applyic-h
d_applyic'45'h_1924 ::
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
  T__'8773'__382 -> T__'8773'__382
d_applyic'45'h_1924 = erased
-- Once.Adequacy.CoherenceHet._.In-h
d_In'45'h_1944 ::
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
  T__'8773'__382 -> T__'8773'__382
d_In'45'h_1944 = erased
-- Once.Adequacy.CoherenceHet._.inlapp-h
d_inlapp'45'h_1968 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__382 -> T__'8773'__382
d_inlapp'45'h_1968 = erased
-- Once.Adequacy.CoherenceHet._.inrapp-h
d_inrapp'45'h_1984 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__382 -> T__'8773'__382
d_inrapp'45'h_1984 = erased
-- Once.Adequacy.CoherenceHet._.initapp-h
d_initapp'45'h_1998 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8773'__382 -> T__'8773'__382
d_initapp'45'h_1998 = erased
-- Once.Adequacy.CoherenceHet._.polydc-go
d_polydc'45'go_2022 ::
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
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 -> T__'8773'__382
d_polydc'45'go_2022 = erased
-- Once.Adequacy.CoherenceHet._.polydd-go
d_polydd'45'go_2050 ::
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
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> T__'8773'__382
d_polydd'45'go_2050 = erased
-- Once.Adequacy.CoherenceHet._.polydc-h
d_polydc'45'h_2102 ::
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
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 -> T__'8773'__382
d_polydc'45'h_2102 = erased
-- Once.Adequacy.CoherenceHet._.polydd-h
d_polydd'45'h_2174 ::
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
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> T__'8773'__382
d_polydd'45'h_2174 = erased
