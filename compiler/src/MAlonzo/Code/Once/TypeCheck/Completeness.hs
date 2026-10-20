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

module MAlonzo.Code.Once.TypeCheck.Completeness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Subset.DecSetoid
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Instance
import qualified MAlonzo.Code.Once.Lang.Type.Join
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type.Instance
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Completeness.Rules
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Completeness.leaf-route
d_leaf'45'route_18 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_AppHeadView_294 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leaf'45'route_18 = erased
-- Once.TypeCheck.Completeness.app-other-route
d_app'45'other'45'route_156 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'other'45'route_156 = erased
-- Once.TypeCheck.Completeness.DPoly.⇒-parts
d_'8658''45'parts_190 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_68 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8658''45'parts_190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8658''45'parts_190
du_'8658''45'parts_190 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8658''45'parts_190
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.TypeCheck.Completeness.DPoly.arrow-parts
d_arrow'45'parts_206 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrow'45'parts_206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_arrow'45'parts_206 v7
du_arrow'45'parts_206 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_arrow'45'parts_206 v0
  = coe seq (coe v0) (coe du_'8658''45'parts_190)
-- Once.TypeCheck.Completeness.DPoly.gp-eq
d_gp'45'eq_242 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gp'45'eq_242 = erased
-- Once.TypeCheck.Completeness.DPoly.gg-eq
d_gg'45'eq_280 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gg'45'eq_280 = erased
-- Once.TypeCheck.Completeness.DPoly.gm-eq
d_gm'45'eq_338 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gm'45'eq_338 = erased
-- Once.TypeCheck.Completeness.DPoly.at-π
d_at'45'π_410 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at'45'π_410 ~v0 v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
              ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22
  = du_at'45'π_410 v1 v2 v3 v6 v7 v9 v18
du_at'45'π_410 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at'45'π_410 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10
              (coe v3) (coe v2) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then case coe v9 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                         -> let v11
                                  = MAlonzo.Code.Once.Type.Match.d_instantiateAcc_92
                                      (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v3))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Poly.d_substPoly_162
                                            (coe v6) (coe v5)))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                            coe
                              (case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                   -> let v13
                                            = MAlonzo.Code.Once.Type.Instance.d_θof_492 (coe v12) in
                                      coe
                                        (let v14
                                               = MAlonzo.Code.Once.Type.Rigid.d_allBase'63'_492
                                                   (coe v13)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.Instance.d_ftvK_8
                                                      (coe v4)) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                -> if coe v15
                                                     then coe
                                                            seq (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe
                                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                                                  (coe
                                                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                     (coe v1)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                        (coe v3))
                                                                     (coe
                                                                        MAlonzo.Code.Once.Lang.Type.Poly.d_substPoly_162
                                                                        (coe v6) (coe v5)))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                                                     (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                                        (coe v1))
                                                                     (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.Poly.d_substPoly_162
                                                                           (coe v6) (coe v5)))
                                                                     v10)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Syntax.C_poly_402
                                                                     v0))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe (0 :: Integer))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe (0 :: Integer)) erased)))
                                                     else (let v17
                                                                 = seq
                                                                     (coe v16)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                        (coe v15)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                           coe
                                                             (case coe v17 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                  -> if coe v18
                                                                       then coe
                                                                              seq (coe v19)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                       (coe v1)
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                          (coe v3))
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Lang.Type.Poly.d_substPoly_162
                                                                                          (coe v6)
                                                                                          (coe v5)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                                                                       (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                                                          (coe v1))
                                                                                       (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Lang.Type.Poly.d_substPoly_162
                                                                                             (coe
                                                                                                v6)
                                                                                             (coe
                                                                                                v5)))
                                                                                       v10)
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_poly_402
                                                                                       v0))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       (0 ::
                                                                                          Integer))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          (0 ::
                                                                                             Integer))
                                                                                       erased)))
                                                                       else coe
                                                                              seq (coe v19)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v9) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.DPoly.at-m
d_at'45'm_654 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at'45'm_654 ~v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
              ~v14 ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21
  = du_at'45'm_654 v1 v2 v3 v6 v7 v8 v9 v16 v18
du_at'45'm_654 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at'45'm_654 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_at'45'π_410 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v6)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Once.Type.Instance.du_instantiate'45'sound_1804
                  (coe v5) (coe v1)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                     (coe
                        MAlonzo.Code.Once.Type.Instance.du_instantiate'45'complete_446
                        (coe v5)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe du_arrow'45'parts_206 (coe v7))))))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_at'45'π_410 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v6)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                     (coe
                        MAlonzo.Code.Once.Type.Instance.du_instantiate'45'sound_1804
                        (coe v5) (coe v1)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Once.Type.Instance.du_instantiate'45'complete_446
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe du_arrow'45'parts_206 (coe v7)))))))))))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        du_at'45'π_410 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v6)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Once.Type.Instance.du_instantiate'45'sound_1804
                              (coe v5) (coe v1)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.Type.Instance.du_instantiate'45'complete_446
                                    (coe v5)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe du_arrow'45'parts_206 (coe v7))))))))))))
            erased))
-- Once.TypeCheck.Completeness.DPoly.from-arrow
d_from'45'arrow_762 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_from'45'arrow_762 ~v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11
                    ~v12 ~v13 ~v14 ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21
  = du_from'45'arrow_762 v1 v2 v3 v8 v9 v16 v18
du_from'45'arrow_762 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_from'45'arrow_762 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_as'45'pure_292
        -> let v9
                 = coe
                     MAlonzo.Code.Data.List.Relation.Binary.Subset.DecSetoid.du__'8838''63'__40
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                        (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
                     (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v4))
                     (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v3)) in
           coe
             (case coe v9 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                  -> if coe v10
                       then coe
                              seq (coe v11)
                              (coe
                                 du_at'45'm_654 (coe v0) (coe v1) (coe v2)
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                                    (coe v3) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                    (coe v4))
                                 (coe v3) (coe v4)
                                 (coe MAlonzo.Code.Once.Lang.Type.Poly.C_as'45'pure_292) (coe v6))
                       else coe
                              seq (coe v11) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Lang.Type.Poly.C_as'45'eff_298
        -> let v9
                 = coe
                     MAlonzo.Code.Data.List.Relation.Binary.Subset.DecSetoid.du__'8838''63'__40
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                        (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
                     (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v4))
                     (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v3)) in
           coe
             (case coe v9 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                  -> if coe v10
                       then coe
                              seq (coe v11)
                              (coe
                                 du_at'45'm_654 (coe v0) (coe v1) (coe v2)
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38)
                                 (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 (coe v3) (coe v4))
                                 (coe v3) (coe v4)
                                 (coe MAlonzo.Code.Once.Lang.Type.Poly.C_as'45'eff_298) (coe v6))
                       else coe
                              seq (coe v11) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Lang.Type.Poly.C_as'45'act_304
        -> let v9
                 = coe
                     MAlonzo.Code.Data.List.Relation.Binary.Subset.DecSetoid.du__'8838''63'__40
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                        (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
                     (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v4))
                     (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v3)) in
           coe
             (case coe v9 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                  -> if coe v10
                       then coe
                              seq (coe v11)
                              (coe
                                 du_at'45'm_654 (coe v0) (coe v1) (coe v2)
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36)
                                 (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 (coe v3) (coe v4))
                                 (coe v3) (coe v4)
                                 (coe MAlonzo.Code.Once.Lang.Type.Poly.C_as'45'act_304) (coe v6))
                       else coe
                              seq (coe v11) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.DPoly.from-lookups
d_from'45'lookups_1126 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_from'45'lookups_1126 ~v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11
                       ~v12 ~v13 ~v14 ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21
  = du_from'45'lookups_1126 v1 v2 v3 v8 v9 v16 v18
du_from'45'lookups_1126 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_from'45'lookups_1126 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_from'45'arrow_762 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v5) (coe v6)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_from'45'arrow_762 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v5) (coe v6))))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        du_from'45'arrow_762 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe v6)))))
            erased))
-- Once.TypeCheck.Completeness.poly-head-fails
d_poly'45'head'45'fails_1180 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'head'45'fails_1180 = erased
-- Once.TypeCheck.Completeness.var-route
d_var'45'route_1216 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_var'45'route_1216 = erased
-- Once.TypeCheck.Completeness.given-infer-route
d_given'45'infer'45'route_1252 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_given'45'infer'45'route_1252 = erased
-- Once.TypeCheck.Completeness.given-infer-complete
d_given'45'infer'45'complete_1460 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'infer'45'complete_1460 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8
                                  ~v9 ~v10 v11 ~v12 ~v13 ~v14
  = du_given'45'infer'45'complete_1460 v2 v3 v4 v5 v6 v11
du_given'45'infer'45'complete_1460 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'infer'45'complete_1460 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
               -> let v13
                        = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
                            (coe v0) (coe v1) in
                  coe
                    (let v14
                           = MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10
                               (coe v4) (coe v3) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                            -> if coe v15
                                 then case coe v16 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                          -> case coe v14 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                 -> if coe v18
                                                      then case coe v19 of
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                                                       (coe
                                                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                          (coe v1)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                             (coe
                                                                                MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                             (coe v4))
                                                                          (coe v2))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                                                          v17
                                                                          (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                                             (coe v2))
                                                                          v20)
                                                                       v10)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v11)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v12) erased))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      else coe
                                                             seq (coe v19)
                                                             (coe
                                                                MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v16)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.given-cata-complete
d_given'45'cata'45'complete_1548 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'cata'45'complete_1548 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
                                 ~v9 v10 v11 ~v12
  = du_given'45'cata'45'complete_1548 v2 v3 v4 v5 v10 v11
du_given'45'cata'45'complete_1548 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'cata'45'complete_1548 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
               -> let v13
                        = coe
                            MAlonzo.Code.Once.Lang.Type.DecEq.du_'8799'T'45''8658''45'aux_152
                            (coe
                               MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
                                  (coe v1))
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
                                  (coe v1)))
                            (coe
                               MAlonzo.Code.Once.Lang.Type.DecEq.du_'8799'k'45'aux_22
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'p__12 (coe v2)
                                  (coe v2)))
                            (coe
                               MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v1)
                               (coe v1)) in
                  coe
                    (case coe v13 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                         -> if coe v14
                              then coe
                                     seq (coe v15)
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_withUnit'45'elim_2446
                                        (coe v4)
                                        (coe
                                           (\ v16 ->
                                              coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v9 v3
                                                   v10)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe addInt (coe (1 :: Integer)) (coe v11))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v12) erased)))))
                              else coe
                                     seq (coe v15)
                                     (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.compose-f-complete
d_compose'45'f'45'complete_1642 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compose'45'f'45'complete_1642 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10
                                ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_compose'45'f'45'complete_1642 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_compose'45'f'45'complete_1642 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compose'45'f'45'complete_1642 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = let v9
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v9 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
           -> case coe v10 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v12 v13 v14 v15 v16
                  -> let v17
                           = coe
                               MAlonzo.Code.Once.Type.Sub.du_arr'45'aux_28
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                               (coe
                                  MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v4) (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v6) (coe v5))
                               (coe
                                  MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10 (coe v8)
                                  (coe v7)) in
                     coe
                       (case coe v17 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                            -> if coe v18
                                 then case coe v19 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                          -> let v21
                                                   = coe
                                                       MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
                                                       (coe v0) (coe v2)
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                          (coe v3)
                                                          (coe
                                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                             (coe
                                                                MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                             (coe v7))
                                                          (coe v4)) in
                                             coe
                                               (case coe v21 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                    -> case coe v22 of
                                                         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v24 v25 v26 v27
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_comp''_452
                                                                   v13 v24 v4
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                                                      (coe
                                                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                         (coe v4)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                            (coe
                                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                            (coe v8))
                                                                         (coe v6))
                                                                      v20 v14)
                                                                   v25)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      addInt (coe (1 :: Integer))
                                                                      (coe
                                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                         (coe v15) (coe v26)))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v27) erased))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v19)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.compose-g-complete
d_compose'45'g'45'complete_1820 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compose'45'g'45'complete_1820 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10
                                ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
  = du_compose'45'g'45'complete_1820 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_compose'45'g'45'complete_1820 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compose'45'g'45'complete_1820 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_258 v12 v13 v14 v15 v16
               -> let v17
                        = coe
                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
                            (coe v0) (coe v1)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v12)
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
                               (coe v5)) in
                  coe
                    (case coe v17 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                         -> case coe v18 of
                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v20 v21 v22 v23
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v20 v13 v12
                                        v21 v14)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           addInt (coe (1 :: Integer))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v22)
                                              (coe v15)))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v23)
                                           erased))
                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v20
                                -> coe
                                     du_compose'45'f'45'complete_1642 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_260 v12
               -> coe
                    du_compose'45'f'45'complete_1642 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.infer-complete-RApp-spine
d_infer'45'complete'45'RApp'45'spine_2070 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'spine_2070 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                          ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_infer'45'complete'45'RApp'45'spine_2070 v0 v1 v2
du_infer'45'complete'45'RApp'45'spine_2070 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'spine_2070 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe
                seq (coe v4)
                (let v6
                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
                           (coe v0) (coe v2) in
                 coe
                   (case coe v6 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                        -> case coe v7 of
                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v9 v10 v11 v12 v13
                               -> let v14
                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6128
                                            (coe v0) (coe v1) (coe v9)
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) in
                                  coe
                                    (case coe v14 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                         -> case coe v15 of
                                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_258 v17 v18 v19 v20 v21
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_app_50
                                                        v18 v10 v9
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                        v19 v11)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           addInt (coe (1 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                              (coe v20) (coe v12)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v21) erased))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.checkElab-fallback-RVar
d_checkElab'45'fallback'45'RVar_2186 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar_2186 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                     ~v8 ~v9
  = du_checkElab'45'fallback'45'RVar_2186 v0 v1 v2 v3
du_checkElab'45'fallback'45'RVar_2186 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar_2186 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_4806
              (coe v0) (coe v2)
              (coe
                 MAlonzo.Code.Once.Lang.Typing.Scope.d_lookupLocal'45'go_162
                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0))
                 (coe v2)
                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v0))
                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0)))
              (coe
                 MAlonzo.Code.Once.Lang.Typing.Scope.d_lookupImport_38
                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v0))
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
                               (coe v3) (coe v1) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                            -> if coe v13
                                 then case coe v14 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v3
                                                  v15 v9)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v11) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v14)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.completeness-gap-inl-app-check-eq
d_completeness'45'gap'45'inl'45'app'45'check'45'eq_2268 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'inl'45'app'45'check'45'eq_2268 v0 v1 v2
                                                        ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2268 v0 v1 v2
du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2268 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2268 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v6 v2
                          (coe MAlonzo.Code.Once.IR.C_inl_54) v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.completeness-gap-inr-app-check-eq
d_completeness'45'gap'45'inr'45'app'45'check'45'eq_2316 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'inr'45'app'45'check'45'eq_2316 v0 v1 ~v2
                                                        v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2316 v0 v1 v3
du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2316 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2316 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v6 v2
                          (coe MAlonzo.Code.Once.IR.C_inr_60) v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.completeness-gap-initial-app-check-eq
d_completeness'45'gap'45'initial'45'app'45'check'45'eq_2362 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'initial'45'app'45'check'45'eq_2362 v0 v1
                                                            ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2362
      v0 v1
du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2362 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2362 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
              (coe v0) (coe v1) (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v5
                          (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                          (coe MAlonzo.Code.Once.IR.C_initial_76) v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v7))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.checkElabV-RResolved-J
d_checkElabV'45'RResolved'45'J_2392 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkElabV'45'RResolved'45'J_2392 = erased
-- Once.TypeCheck.Completeness.caseGo-success
d_caseGo'45'success_2438 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caseGo'45'success_2438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 v13 v14 v15 ~v16 ~v17 ~v18
  = du_caseGo'45'success_2438 v13 v14 v15
du_caseGo'45'success_2438 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caseGo'45'success_2438 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v0) (coe v2)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased)
-- Once.TypeCheck.Completeness.check-completeV
d_check'45'completeV_2468 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'completeV_2468 v0 v1 v2 ~v3 v4
  = du_check'45'completeV_2468 v0 v1 v2 v4
du_check'45'completeV_2468 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'completeV_2468 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
              (coe v0) (coe v1) (coe v2) in
    coe
      (let v5
             = coe
                 du_check'45'complete_2644 (coe v0) (coe v1) (coe v2) (coe v3) in
       coe
         (case coe v4 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
              -> case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> case coe v9 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v7) erased)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Completeness.iFromInferSub
d_iFromInferSub_2486 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_iFromInferSub_2486 v0 v1 v2 v3 ~v4 v5
  = du_iFromInferSub_2486 v0 v1 v2 v3 v5
du_iFromInferSub_2486 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_iFromInferSub_2486 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v7
               -> coe
                    (\ v8 ->
                       seq
                         (coe v8)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RInt_16
                            (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'float_42
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v10 v11 v12 v13
               -> coe
                    (\ v14 ->
                       seq
                         (coe v14)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RFloat_52
                            (coe v10) (coe v11) (coe v12)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit_46
        -> coe
             (\ v6 ->
                seq
                  (coe v6)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RUnit_98))
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
        -> coe
             (\ v6 ->
                seq
                  (coe v6)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'unit_2212))
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v11
               -> coe
                    (\ v12 ->
                       coe
                         du_checkElab'45'fallback'45'RVar_2186 (coe v0) (coe v3) (coe v11)
                         (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_70 v8 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RResolved_134
                         (coe v0) (coe v3) (coe v11) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_78
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v11
                      -> case coe v11 of
                           (:) v12 v13
                             -> coe
                                  (\ v14 ->
                                     coe
                                       MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RResolved_134
                                       (coe v0) (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v12)
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                       (coe v2))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_86 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v12
               -> coe
                    (\ v13 ->
                       coe
                         du_checkElab'45'fallback'45'RVar_2186 (coe v0) (coe v3) (coe v12)
                         (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_102 v8 v9 v10 v11 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v17
               -> coe
                    (\ v18 ->
                       coe
                         du_checkElab'45'fallback'45'RVar_2186 (coe v0) (coe v3) (coe v17)
                         (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'annot_112 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_58 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RAnnot_984
                         (coe v0) (coe v3) (coe v11) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_128 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
                      -> coe
                           (\ v18 ->
                              case coe v18 of
                                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'prod_62 v23 v24
                                  -> case coe v3 of
                                       MAlonzo.Code.Once.Lang.Type.C__'42'__24 v25 v26
                                         -> let v27
                                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         du_iFromInferSub_2486 v0 v14 v16 v25 v12
                                                         v23) in
                                            coe
                                              (let v28
                                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               du_iFromInferSub_2486 v0 v14 v16 v25
                                                               v12 v23)) in
                                               coe
                                                 (coe
                                                    du_pair'45'lit'45'reduce_2544 (coe v10)
                                                    (coe v11) (coe v27) (coe v28)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                       (coe
                                                          du_iFromInferSub_2486 v0 v15 v17 v26 v13
                                                          v24))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             du_iFromInferSub_2486 v0 v15 v17 v26
                                                             v13 v24)))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                             (coe
                                                                du_iFromInferSub_2486 v0 v15 v17 v26
                                                                v13 v24))))))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_136 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62 v10
               -> coe
                    (\ v11 ->
                       seq
                         (coe v11)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RUnaryOp_1602
                            (coe v0) (coe v10) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg'45'float_148
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62 v11
               -> coe
                    (\ v12 ->
                       seq
                         (coe v12)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RUnaryOp_1602
                            (coe v0) (coe v11) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'let_168 v9 v11 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v16 v17 v18
               -> coe
                    (\ v19 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RLet_1162
                         (coe v0) (coe v3) (coe v16) (coe v17) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case_202 v11 v12 v13 v14 v16 v17 v18 v19 v20 v21 v22 v23 v24
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v25 v26 v27 v28 v29
               -> coe
                    (\ v30 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RDestruct_1372
                         (coe v0) (coe v3) (coe v25) (coe v26) (coe v27) (coe v28)
                         (coe v29))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_216 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_6152
                         (coe v0) (coe v3) (coe v14) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_230 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_6152
                         (coe v0) (coe v3) (coe v14) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_244 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_6152
                         (coe v0) (coe v3) (coe v14) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_258 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_6152
                         (coe v0) (coe v3) (coe v14) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_272 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_6152
                         (coe v0) (coe v3) (coe v14) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_282 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'id_4996
                         (coe v0) (coe v3) (coe v11) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_294 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'fst_5084
                         (coe v0) (coe v3) (coe v12) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_306 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'snd_5172
                         (coe v0) (coe v3) (coe v12) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_316 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'terminal_5972
                         (coe v0) (coe v3) (coe v11)
                         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_328 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply_3150
                         (coe v0) (coe v3) (coe v12) (coe v7) (coe v2) (coe v9)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               du_infer'45'complete_2576 (coe v0) (coe v12)
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                     (coe v2))
                                  (coe v7))
                               (coe v10)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  du_infer'45'complete_2576 (coe v0) (coe v12)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                        (coe v2))
                                     (coe v7))
                                  (coe v10))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     du_infer'45'complete_2576 (coe v0) (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                           (coe v2))
                                        (coe v7))
                                     (coe v10))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_344 v7 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
                      -> case coe v11 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_eg'45'act_58
                             -> coe
                                  (\ v18 ->
                                     coe
                                       MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3302
                                       (coe v0) (coe v3) (coe v14) (coe v7) (coe v17) (coe v9)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             du_infer'45'complete_2576 (coe v0) (coe v14)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                   (coe v7)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                                                   (coe v17))
                                                (coe v7))
                                             (coe v12)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                du_infer'45'complete_2576 (coe v0) (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v7)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                                                      (coe v17))
                                                   (coe v7))
                                                (coe v12))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   du_infer'45'complete_2576 (coe v0) (coe v14)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                         (coe v7)
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                            (coe
                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                            (coe
                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                                                         (coe v17))
                                                      (coe v7))
                                                   (coe v12))))))
                           MAlonzo.Code.Once.Lang.Type.Grade.C_eg'45'eff_60
                             -> coe
                                  (\ v18 ->
                                     coe
                                       MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3226
                                       (coe v0) (coe v3) (coe v14) (coe v7) (coe v17) (coe v9)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             du_infer'45'complete_2576 (coe v0) (coe v14)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                   (coe v7)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
                                                   (coe v17))
                                                (coe v7))
                                             (coe v12)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                du_infer'45'complete_2576 (coe v0) (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v7)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
                                                      (coe v17))
                                                   (coe v7))
                                                (coe v12))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   du_infer'45'complete_2576 (coe v0) (coe v14)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                         (coe v7)
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                            (coe
                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                            (coe
                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
                                                         (coe v17))
                                                      (coe v7))
                                                   (coe v12))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_356 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> coe
                    (\ v15 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'Out_6060
                         (coe v0) (coe v3) (coe v14)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v7)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v7)
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_368 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> coe
                    (\ v15 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'Out_6060
                         (coe v0) (coe v3) (coe v14)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                            (coe
                               MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v7)
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v7)
                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app_386 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> coe
                    (\ v18 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic_5276
                         (coe v0) (coe v3) (coe v16) (coe v17) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_406 v8 v10 v11 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v22 v23
                             -> coe
                                  (\ v24 ->
                                     coe
                                       MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic_5276
                                       (coe v0) (coe v3) (coe v17) (coe v18)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                          (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v23))
                                          (coe v21)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_422 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic_5276
                         (coe v0) (coe v3) (coe v15) (coe v16) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.check-completeV-from-infer
d_check'45'completeV'45'from'45'infer_2506 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'completeV'45'from'45'infer_2506 v0 v1 v2 v3 ~v4 v5 v6
  = du_check'45'completeV'45'from'45'infer_2506 v0 v1 v2 v3 v5 v6
du_check'45'completeV'45'from'45'infer_2506 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'completeV'45'from'45'infer_2506 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
              (coe v0) (coe v1) (coe v3) in
    coe
      (let v7 = coe du_iFromInferSub_2486 v0 v1 v2 v3 v4 v5 in
       coe
         (case coe v6 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
              -> case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                     -> case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v13 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v9) erased)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Completeness.pair-lit-reduce
d_pair'45'lit'45'reduce_2544 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair'45'lit'45'reduce_2544 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9
                             ~v10 v11 v12 v13 ~v14 ~v15 ~v16
  = du_pair'45'lit'45'reduce_2544 v5 v6 v7 v8 v11 v12 v13
du_pair'45'lit'45'reduce_2544 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair'45'lit'45'reduce_2544 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v0 v1 v2 v4)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) erased))
-- Once.TypeCheck.Completeness.iFromInfer
d_iFromInfer_2560 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_iFromInfer_2560 v0 v1 v2 ~v3 v4 = du_iFromInfer_2560 v0 v1 v2 v4
du_iFromInfer_2560 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_iFromInfer_2560 v0 v1 v2 v3
  = coe
      du_iFromInferSub_2486 v0 v1 v2 v2 v3
      (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98 (coe v2))
-- Once.TypeCheck.Completeness.infer-complete
d_infer'45'complete_2576 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete_2576 v0 v1 v2 ~v3 v4
  = du_infer'45'complete_2576 v0 v1 v2 v4
du_infer'45'complete_2576 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete_2576 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RInt_18
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'float_42
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_float_198
                       (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                          (coe v9) (coe v10) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                          erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit_46
        -> coe
             MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RUnit_30
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
        -> coe
             MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RVar'45'unit_40
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RVar'45'local_984
             (coe v8)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_70 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RResolved_56
                    (coe v10) (coe v2) (coe v7) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_78
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v10
                      -> case coe v10 of
                           (:) v11 v12
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RResolved'45'own_258
                                  (coe v11)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_86 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RVar'45'import_1024
                    (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_102 v7 v8 v9 v10 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'poly'45'infer_4956
                    (coe v16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'annot_112 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_58 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RAnnot_464
                    (coe v0) (coe v10) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_128 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v13 v14
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RPair_336
                    (coe v0) (coe v13) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_136 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62 v9
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RUnaryOp'45'neg_394
                    (coe v0) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg'45'float_148
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v11 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_float_198
                              (MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                                 (coe
                                    MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v11)
                                    (coe v12) (coe v13))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'let_168 v8 v10 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RLet_526
                    (coe v0) (coe v15) (coe v16) (coe v17)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case_202 v10 v11 v12 v13 v15 v16 v17 v18 v19 v20 v21 v22 v23
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v24 v25 v26 v27 v28
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RDestruct_1774
                    (coe v0) (coe v24) (coe v25) (coe v26) (coe v27) (coe v28)
                    (coe v12) (coe v13) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_216 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RBinOp'45'arith_1466
                    (coe v0) (coe v13) (coe v14) (coe v15) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v14)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v14)
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v15)
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2576 (coe v0) (coe v15)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_230 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RBinOp'45'arith'45'float_1360
                    (coe v0) (coe v13) (coe v14) (coe v15) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v14)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v12)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v14)
                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v15)
                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v12))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2576 (coe v0) (coe v15)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_244 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1156
                    (coe v0) (coe v13) (coe v14) (coe v15) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v14)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v12)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v14)
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v15)
                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v12))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2576 (coe v0) (coe v15)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_258 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1258
                    (coe v0) (coe v13) (coe v14) (coe v15) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v14)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v14)
                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v15)
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2576 (coe v0) (coe v15)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_272 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RBinOp'45'cmp_1576
                    (coe v0) (coe v13) (coe v14) (coe v15) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v14)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v14)
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v15)
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2576 (coe v0) (coe v15)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_282 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'id_598
                    (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_294 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'fst_800
                    (coe v0) (coe v11) (coe v2) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v11)
                          (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v7))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v11)
                             (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v7))
                             (coe v9))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2576 (coe v0) (coe v11)
                                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v7))
                                (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_306 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'snd_832
                    (coe v0) (coe v11) (coe v6) (coe v2) (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v11)
                          (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v6) (coe v2))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v11)
                             (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v6) (coe v2))
                             (coe v9))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2576 (coe v0) (coe v11)
                                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v6) (coe v2))
                                (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_316 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'terminal_636
                    (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_328 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'apply_864
                    (coe v0) (coe v11) (coe v6) (coe v2) (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v11)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'42'__24
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                (coe v2))
                             (coe v6))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v11)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                   (coe v2))
                                (coe v6))
                             (coe v9))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2576 (coe v0) (coe v11)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                      (coe v2))
                                   (coe v6))
                                (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_344 v6 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
                      -> case coe v10 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_eg'45'act_58
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'apply'45'act_948
                                  (coe v0) (coe v13) (coe v6) (coe v16) (coe v8)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        du_infer'45'complete_2576 (coe v0) (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                              (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                                              (coe v16))
                                           (coe v6))
                                        (coe v11)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           du_infer'45'complete_2576 (coe v0) (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                 (coe v6)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                                                 (coe v16))
                                              (coe v6))
                                           (coe v11))))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              du_infer'45'complete_2576 (coe v0) (coe v13)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                                                    (coe v16))
                                                 (coe v6))
                                              (coe v11)))))
                           MAlonzo.Code.Once.Lang.Type.Grade.C_eg'45'eff_60
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'apply'45'eff_906
                                  (coe v0) (coe v13) (coe v6) (coe v16) (coe v8)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        du_infer'45'complete_2576 (coe v0) (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                              (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
                                              (coe v16))
                                           (coe v6))
                                        (coe v11)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           du_infer'45'complete_2576 (coe v0) (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                 (coe v6)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
                                                 (coe v16))
                                              (coe v6))
                                           (coe v11))))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              du_infer'45'complete_2576 (coe v0) (coe v13)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
                                                    (coe v16))
                                                 (coe v6))
                                              (coe v11)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_356 v6 v8 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'Out_676
                    (coe v0) (coe v13) (coe v6) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_368 v6 v8 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'Out'45'act_738
                    (coe v0) (coe v13) (coe v6) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app_386 v7 v9 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'generic_1944
                    (coe v0) (coe v15) (coe v16) (coe v7) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_406 v7 v9 v10 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v12 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_eg'45'act_58
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'act_2170
                           (coe v0) (coe v16) (coe v17) (coe v7)
                    MAlonzo.Code.Once.Lang.Type.Grade.C_eg'45'eff_60
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'eff_2072
                           (coe v0) (coe v16) (coe v17) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_422 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v14 v15
               -> coe
                    du_spine'45'complete_2598 (coe v0) (coe v14) (coe v15) (coe v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.spine-complete
d_spine'45'complete_2598 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spine'45'complete_2598 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_spine'45'complete_2598 v0 v1 v2 v9
du_spine'45'complete_2598 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spine'45'complete_2598 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_790 v7 v10 v12 v13 v14
        -> coe
             seq (coe v14)
             (coe
                MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'generic_1944
                (coe v0) (coe v1) (coe v2) (coe v7)
                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_814 v9 v10 v11 v12 v13 v14 v19 v20 v21 v22
        -> coe
             du_infer'45'complete'45'RApp'45'spine_2070 (coe v0) (coe v1)
             (coe v2)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_834 v9 v12 v13
        -> coe
             du_infer'45'complete'45'RApp'45'spine_2070 (coe v0) (coe v1)
             (coe v2)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_854 v8 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
                      -> coe
                           du_infer'45'complete'45'RApp'45'spine_2070 (coe v0)
                           (coe
                              MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
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
                                             (coe ("compose" :: Data.Text.Text))
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                 (coe v18))
                              (coe v16))
                           (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_930 v9 v10 v13 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
                      -> coe
                           du_infer'45'complete'45'RApp'45'spine_2070 (coe v0)
                           (coe
                              MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
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
                                             (coe ("case" :: Data.Text.Text))
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                 (coe v21))
                              (coe v19))
                           (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_950 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
                      -> coe
                           du_infer'45'complete'45'RApp'45'spine_2070 (coe v0)
                           (coe
                              MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
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
                                             (coe ("pair" :: Data.Text.Text))
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                 (coe v18))
                              (coe v16))
                           (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_966 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> coe
                    du_infer'45'complete'45'RApp'45'spine_2070 (coe v0)
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
                                   (coe ("cata" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v14))
                    (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.given-complete
d_given'45'complete_2618 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'complete_2618 v0 v1 v2 v3 v4 ~v5 v6
  = du_given'45'complete_2618 v0 v1 v2 v3 v4 v6
du_given'45'complete_2618 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'complete_2618 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_790 v9 v12 v14 v15 v16
        -> coe
             du_given'45'infer'45'complete_1460 (coe v2) (coe v9) (coe v3)
             (coe v4) (coe v12)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_814 v11 v12 v13 v14 v15 v16 v21 v22 v23 v24
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v25
               -> case coe v23 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                      -> coe
                           seq (coe v27)
                           (coe
                              du_from'45'lookups_1126 (coe v25) (coe v2) (coe v4) (coe v13)
                              (coe v14) (coe v21) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_834 v11 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v16 v17
               -> let v18
                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
                            (coe
                               MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                               (coe v16) (coe v2))
                            (coe v17) in
                  coe
                    (let v19
                           = coe
                               du_infer'45'complete_2576
                               (coe
                                  MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                                  (coe v16) (coe v2))
                               (coe v17) (coe v3) (coe v15) in
                     coe
                       (case coe v18 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                            -> case coe v20 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v22 v23 v24 v25 v26
                                   -> case coe v23 of
                                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v28 v29
                                          -> case coe v19 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                 -> case coe v31 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                        -> coe
                                                             seq (coe v33)
                                                             (let v34
                                                                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1302
                                                                        (coe v28)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) in
                                                              coe
                                                                (let v35
                                                                       = coe
                                                                           MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_decideLeq'45'just_1598
                                                                           (coe v28)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) in
                                                                 coe
                                                                   (coe
                                                                      seq (coe v34)
                                                                      (coe
                                                                         seq (coe v35)
                                                                         (coe
                                                                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_withUnit'45'elim_2446
                                                                            (coe v14)
                                                                            (coe
                                                                               (\ v36 ->
                                                                                  coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_lam_34
                                                                                       v28 v24)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe v25))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe v26)
                                                                                          erased)))))))))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_854 v10 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v19 v20
                      -> let v21
                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6128
                                   (coe v0) (coe v18) (coe v2) (coe v4) in
                         coe
                           (let v22
                                  = coe
                                      du_given'45'complete_2618 (coe v0) (coe v18) (coe v2)
                                      (coe v10) (coe v4) (coe v15) in
                            coe
                              (case coe v21 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                   -> case coe v23 of
                                        MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_258 v25 v26 v27 v28 v29
                                          -> case coe v22 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                 -> case coe v31 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                        -> case coe v33 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                               -> let v36
                                                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6128
                                                                            (coe v0) (coe v20)
                                                                            (coe v25) (coe v4) in
                                                                  coe
                                                                    (let v37
                                                                           = coe
                                                                               du_given'45'complete_2618
                                                                               (coe v0) (coe v20)
                                                                               (coe v25) (coe v3)
                                                                               (coe v4) (coe v16) in
                                                                     coe
                                                                       (case coe v36 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                            -> case coe v38 of
                                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_258 v40 v41 v42 v43 v44
                                                                                   -> case coe
                                                                                             v37 of
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v45 v46
                                                                                          -> case coe
                                                                                                    v46 of
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v47 v48
                                                                                                 -> coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v48)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Surface.Syntax.C_comp''_452
                                                                                                            v41
                                                                                                            v26
                                                                                                            v25
                                                                                                            v42
                                                                                                            v27)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                            (coe
                                                                                                               addInt
                                                                                                               (coe
                                                                                                                  (1 ::
                                                                                                                     Integer))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                  (coe
                                                                                                                     v43)
                                                                                                                  (coe
                                                                                                                     v28)))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               (coe
                                                                                                                  v44)
                                                                                                               erased)))
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'id_864 v9
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_withUnit'45'elim_2446
             (coe v9)
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                        (coe MAlonzo.Code.Once.IR.C_id_20))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                           erased))))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_876 v10
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_withUnit'45'elim_2446
             (coe v10)
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                        (coe MAlonzo.Code.Once.IR.C_fst_42))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                           erased))))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_888 v10
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_withUnit'45'elim_2446
             (coe v10)
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                        (coe MAlonzo.Code.Once.IR.C_snd_48))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                           erased))))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_898 v9
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_withUnit'45'elim_2446
             (coe v9)
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                        (coe MAlonzo.Code.Once.IR.C_terminal_72))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                           erased))))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_906 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_withUnit'45'elim_2446
             (coe v8)
             (coe
                (\ v9 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                        (coe MAlonzo.Code.Once.IR.C_initial_76))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                           erased))))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_930 v11 v12 v15 v16 v17 v18 v19
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v22 v23
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v24 v25
                             -> let v26
                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6128
                                          (coe v0) (coe v23) (coe v24) (coe v4) in
                                coe
                                  (let v27
                                         = coe
                                             du_given'45'complete_2618 (coe v0) (coe v23) (coe v24)
                                             (coe v11) (coe v4) (coe v17) in
                                   coe
                                     (case coe v26 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                          -> case coe v28 of
                                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_258 v30 v31 v32 v33 v34
                                                 -> case coe v27 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                        -> case coe v36 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                               -> case coe v38 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                                      -> let v41
                                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6128
                                                                                   (coe v0)
                                                                                   (coe v21)
                                                                                   (coe v25)
                                                                                   (coe v4) in
                                                                         coe
                                                                           (let v42
                                                                                  = coe
                                                                                      du_given'45'complete_2618
                                                                                      (coe v0)
                                                                                      (coe v21)
                                                                                      (coe v25)
                                                                                      (coe v12)
                                                                                      (coe v4)
                                                                                      (coe v18) in
                                                                            coe
                                                                              (case coe v41 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v43 v44
                                                                                   -> case coe
                                                                                             v43 of
                                                                                        MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_258 v45 v46 v47 v48 v49
                                                                                          -> case coe
                                                                                                    v42 of
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v50 v51
                                                                                                 -> case coe
                                                                                                           v51 of
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v52 v53
                                                                                                        -> coe
                                                                                                             seq
                                                                                                             (coe
                                                                                                                v53)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Once.Surface.Syntax.C_copair''_470
                                                                                                                   v31
                                                                                                                   v46
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                                                         (coe
                                                                                                                            v24)
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                                                            (coe
                                                                                                                               v4))
                                                                                                                         (coe
                                                                                                                            v30))
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                                                                                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                                                                                            (coe
                                                                                                                               v24))
                                                                                                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
                                                                                                                            (coe
                                                                                                                               v30)
                                                                                                                            (coe
                                                                                                                               v3)
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Once.Lang.Type.Sub.d_left_256
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Once.Lang.Type.Join.d_sound_658
                                                                                                                                  (coe
                                                                                                                                     v30)
                                                                                                                                  (coe
                                                                                                                                     v45)
                                                                                                                                  (coe
                                                                                                                                     v3)
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Once.Lang.Type.Join.du_join'63''45'complete_850
                                                                                                                                        (coe
                                                                                                                                           v30)
                                                                                                                                        (coe
                                                                                                                                           v45))))))
                                                                                                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                                                                                                            (coe
                                                                                                                               v4)))
                                                                                                                      v32)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                                                         (coe
                                                                                                                            v25)
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                                                            (coe
                                                                                                                               v4))
                                                                                                                         (coe
                                                                                                                            v45))
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52
                                                                                                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_98
                                                                                                                            (coe
                                                                                                                               v25))
                                                                                                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
                                                                                                                            (coe
                                                                                                                               v45)
                                                                                                                            (coe
                                                                                                                               v3)
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Once.Lang.Type.Sub.d_right_258
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Once.Lang.Type.Join.d_sound_658
                                                                                                                                  (coe
                                                                                                                                     v30)
                                                                                                                                  (coe
                                                                                                                                     v45)
                                                                                                                                  (coe
                                                                                                                                     v3)
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Once.Lang.Type.Join.du_join'63''45'complete_850
                                                                                                                                        (coe
                                                                                                                                           v30)
                                                                                                                                        (coe
                                                                                                                                           v45))))))
                                                                                                                         (MAlonzo.Code.Once.Lang.Type.Sub.d_'8849'π'45'refl_94
                                                                                                                            (coe
                                                                                                                               v4)))
                                                                                                                      v47))
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      addInt
                                                                                                                      (coe
                                                                                                                         (1 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                         (coe
                                                                                                                            v33)
                                                                                                                         (coe
                                                                                                                            v48)))
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                      (coe
                                                                                                                         v49)
                                                                                                                      erased)))
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_950 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v19 v20
                      -> case coe v3 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v21 v22
                             -> let v23
                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6128
                                          (coe v0) (coe v20) (coe v2) (coe v4) in
                                coe
                                  (let v24
                                         = coe
                                             du_given'45'complete_2618 (coe v0) (coe v20) (coe v2)
                                             (coe v21) (coe v4) (coe v15) in
                                   coe
                                     (case coe v23 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                          -> case coe v25 of
                                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_258 v27 v28 v29 v30 v31
                                                 -> case coe v24 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                        -> case coe v33 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                               -> case coe v35 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                      -> let v38
                                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6128
                                                                                   (coe v0)
                                                                                   (coe v18)
                                                                                   (coe v2)
                                                                                   (coe v4) in
                                                                         coe
                                                                           (let v39
                                                                                  = coe
                                                                                      du_given'45'complete_2618
                                                                                      (coe v0)
                                                                                      (coe v18)
                                                                                      (coe v2)
                                                                                      (coe v22)
                                                                                      (coe v4)
                                                                                      (coe v16) in
                                                                            coe
                                                                              (case coe v38 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                                                   -> case coe
                                                                                             v40 of
                                                                                        MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_258 v42 v43 v44 v45 v46
                                                                                          -> case coe
                                                                                                    v39 of
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v47 v48
                                                                                                 -> case coe
                                                                                                           v48 of
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v49 v50
                                                                                                        -> coe
                                                                                                             seq
                                                                                                             (coe
                                                                                                                v50)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Once.Surface.Syntax.C_fork''_488
                                                                                                                   v28
                                                                                                                   v43
                                                                                                                   v29
                                                                                                                   v44)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      addInt
                                                                                                                      (coe
                                                                                                                         (1 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                         (coe
                                                                                                                            v30)
                                                                                                                         (coe
                                                                                                                            v45)))
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                      (coe
                                                                                                                         v46)
                                                                                                                      erased)))
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_966 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v17
                      -> coe
                           du_given'45'cata'45'complete_1548 (coe v17) (coe v3) (coe v4)
                           (coe v13) (coe v12)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                              (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.nothing≢just
d_nothing'8802'just_2628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_nothing'8802'just_2628 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_nothing'8802'just_2628
du_nothing'8802'just_2628 :: AgdaAny
du_nothing'8802'just_2628 = MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.check-complete
d_check'45'complete_2644 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete_2644 v0 v1 v2 ~v3 v4
  = du_check'45'complete_2644 v0 v1 v2 v4
du_check'45'complete_2644 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete_2644 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'check_432 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'id_2486
                    (coe v8) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'check_444 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v9 v10 v11
               -> case coe v9 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v12 v13
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'fst_2544
                           (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'check_456 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v9 v10 v11
               -> case coe v9 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v12 v13
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'snd_2602
                           (coe v13) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_466 v7
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'terminal_2658
             (coe v7)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'morph'45'check_476 v7
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'initial_2720
             (coe v7)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'morph'45'check_488 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'inl_2754
                    (coe v9) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'morph'45'check_500 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'inr_2812
                    (coe v9) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'g_520 v8 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v22 v23
                                    -> let v24
                                             = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6128
                                                 (coe v0) (coe v16) (coe v19) (coe v23) in
                                       coe
                                         (let v25
                                                = coe
                                                    du_given'45'complete_2618 (coe v0) (coe v16)
                                                    (coe v19) (coe v8) (coe v23) (coe v13) in
                                          coe
                                            (case coe v24 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                 -> case coe v26 of
                                                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_258 v28 v29 v30 v31 v32
                                                        -> case coe v25 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                               -> case coe v34 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                      -> case coe v36 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                                             -> let v39
                                                                                      = coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
                                                                                          (coe v0)
                                                                                          (coe v18)
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                             (coe
                                                                                                v28)
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                                (coe
                                                                                                   v23))
                                                                                             (coe
                                                                                                v21)) in
                                                                                coe
                                                                                  (let v40
                                                                                         = coe
                                                                                             du_check'45'complete_2644
                                                                                             (coe
                                                                                                v0)
                                                                                             (coe
                                                                                                v18)
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                                (coe
                                                                                                   v28)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                                   (coe
                                                                                                      v23))
                                                                                                (coe
                                                                                                   v21))
                                                                                             (coe
                                                                                                v14) in
                                                                                   coe
                                                                                     (case coe
                                                                                             v39 of
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                                                                          -> case coe
                                                                                                    v41 of
                                                                                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v43 v44 v45 v46
                                                                                                 -> case coe
                                                                                                           v40 of
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v47 v48
                                                                                                        -> case coe
                                                                                                                  v48 of
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v49 v50
                                                                                                               -> coe
                                                                                                                    seq
                                                                                                                    (coe
                                                                                                                       v50)
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_comp''_452
                                                                                                                          v43
                                                                                                                          v29
                                                                                                                          v28
                                                                                                                          v44
                                                                                                                          v30)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                          (coe
                                                                                                                             addInt
                                                                                                                             (coe
                                                                                                                                (1 ::
                                                                                                                                   Integer))
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                (coe
                                                                                                                                   v45)
                                                                                                                                (coe
                                                                                                                                   v31)))
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                             (coe
                                                                                                                                v46)
                                                                                                                             erased)))
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'f_544 v8 v10 v12 v13 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v22 v23 v24
                             -> case coe v23 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v25 v26
                                    -> coe
                                         du_compose'45'g'45'complete_1820 (coe v0) (coe v21)
                                         (coe v19) (coe v22) (coe v8) (coe v24) (coe v10) (coe v26)
                                         (coe v12)
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6128
                                            (coe v0) (coe v19) (coe v22) (coe v26))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case'45'copair'45'check_564 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                             -> case coe v19 of
                                  MAlonzo.Code.Once.Lang.Type.C__'43'__26 v22 v23
                                    -> case coe v20 of
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v24 v25
                                           -> case coe v25 of
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Once.Surface.Syntax.C_copair''_470
                                                          v11 v12
                                                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                du_check'45'completeV_2468 (coe v0)
                                                                (coe v18)
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                   (coe v22)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                      (coe
                                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                      (coe v25))
                                                                   (coe v21))
                                                                (coe v13)))
                                                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                du_check'45'completeV_2468 (coe v0)
                                                                (coe v16)
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                   (coe v23)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                      (coe
                                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                      (coe v25))
                                                                   (coe v21))
                                                                (coe v14))))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                du_caseGo'45'success_2438
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                      (coe
                                                                         du_check'45'completeV_2468
                                                                         (coe v0) (coe v18)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                            (coe v22)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                               (coe v25))
                                                                            (coe v21))
                                                                         (coe v13))))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                         (coe
                                                                            du_check'45'completeV_2468
                                                                            (coe v0) (coe v18)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                               (coe v22)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                  (coe v25))
                                                                               (coe v21))
                                                                            (coe v13)))))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                      (coe
                                                                         du_check'45'completeV_2468
                                                                         (coe v0) (coe v16)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                            (coe v23)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                               (coe v25))
                                                                            (coe v21))
                                                                         (coe v14))))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                   (coe
                                                                      du_caseGo'45'success_2438
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                            (coe
                                                                               du_check'45'completeV_2468
                                                                               (coe v0) (coe v18)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                  (coe v22)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                     (coe v25))
                                                                                  (coe v21))
                                                                               (coe v13))))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                               (coe
                                                                                  du_check'45'completeV_2468
                                                                                  (coe v0) (coe v18)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                     (coe v22)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                        (coe v25))
                                                                                     (coe v21))
                                                                                  (coe v13)))))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                            (coe
                                                                               du_check'45'completeV_2468
                                                                               (coe v0) (coe v16)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                  (coe v23)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                     (coe v25))
                                                                                  (coe v21))
                                                                               (coe v14)))))))
                                                             erased))
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                                                  -> let v26
                                                           = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  du_check'45'complete_2644 (coe v0)
                                                                  (coe v18)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                     (coe v22)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                        (coe v25))
                                                                     (coe v21))
                                                                  (coe v13)) in
                                                     coe
                                                       (let v27
                                                              = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        du_check'45'complete_2644
                                                                        (coe v0) (coe v18)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                           (coe v22)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                              (coe v25))
                                                                           (coe v21))
                                                                        (coe v13))) in
                                                        coe
                                                          (let v28
                                                                 = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                           (coe
                                                                              du_check'45'complete_2644
                                                                              (coe v0) (coe v18)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                 (coe v22)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                    (coe v25))
                                                                                 (coe v21))
                                                                              (coe v13)))) in
                                                           coe
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_copair''_470
                                                                   v11 v12 v26
                                                                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                      (coe
                                                                         du_check'45'complete_2644
                                                                         (coe v0) (coe v16)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                            (coe v23)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                               (coe v25))
                                                                            (coe v21))
                                                                         (coe v14))))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      addInt (coe (1 :: Integer))
                                                                      (coe
                                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                         (coe v27)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                               (coe
                                                                                  du_check'45'complete_2644
                                                                                  (coe v0) (coe v16)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                     (coe v23)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                        (coe v25))
                                                                                     (coe v21))
                                                                                  (coe v14))))))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v28) erased)))))
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
                                                  -> let v26
                                                           = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  du_check'45'complete_2644 (coe v0)
                                                                  (coe v18)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                     (coe v22)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                        (coe v25))
                                                                     (coe v21))
                                                                  (coe v13)) in
                                                     coe
                                                       (let v27
                                                              = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        du_check'45'complete_2644
                                                                        (coe v0) (coe v18)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                           (coe v22)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                              (coe v25))
                                                                           (coe v21))
                                                                        (coe v13))) in
                                                        coe
                                                          (let v28
                                                                 = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                           (coe
                                                                              du_check'45'complete_2644
                                                                              (coe v0) (coe v18)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                 (coe v22)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                    (coe v25))
                                                                                 (coe v21))
                                                                              (coe v13)))) in
                                                           coe
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_copair''_470
                                                                   v11 v12 v26
                                                                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                      (coe
                                                                         du_check'45'complete_2644
                                                                         (coe v0) (coe v16)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                            (coe v23)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                               (coe v25))
                                                                            (coe v21))
                                                                         (coe v14))))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      addInt (coe (1 :: Integer))
                                                                      (coe
                                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                         (coe v27)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                               (coe
                                                                                  du_check'45'complete_2644
                                                                                  (coe v0) (coe v16)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                                     (coe v23)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                                        (coe v25))
                                                                                     (coe v21))
                                                                                  (coe v14))))))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v28) erased)))))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'morph'45'check_584 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v22 v23
                                    -> case coe v21 of
                                         MAlonzo.Code.Once.Lang.Type.C__'42'__24 v24 v25
                                           -> let v26
                                                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           du_check'45'complete_2644 (coe v0)
                                                           (coe v18)
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                              (coe v19)
                                                              (coe
                                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                 (coe
                                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                 (coe v23))
                                                              (coe v24))
                                                           (coe v13)) in
                                              coe
                                                (let v27
                                                       = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 du_check'45'complete_2644 (coe v0)
                                                                 (coe v18)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                    (coe v19)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                       (coe
                                                                          MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                       (coe v23))
                                                                    (coe v24))
                                                                 (coe v13))) in
                                                 coe
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Syntax.C_fork''_488
                                                         v11 v12 v26
                                                         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                            (coe
                                                               du_check'45'complete_2644 (coe v0)
                                                               (coe v16)
                                                               (coe
                                                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                  (coe v19)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                     (coe
                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                     (coe v23))
                                                                  (coe v25))
                                                               (coe v14))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            addInt (coe (1 :: Integer))
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                               (coe v27)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        du_check'45'complete_2644
                                                                        (coe v0) (coe v16)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                           (coe v19)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                              (coe v23))
                                                                           (coe v25))
                                                                        (coe v14))))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        du_check'45'complete_2644
                                                                        (coe v0) (coe v16)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                           (coe v19)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                              (coe v23))
                                                                           (coe v25))
                                                                        (coe v14)))))
                                                            erased))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'curry'45'check_604 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
                      -> case coe v18 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v22 v23
                                    -> let v24
                                             = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    du_check'45'complete_2644 (coe v0) (coe v15)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                          (coe v16) (coe v19))
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                          (coe
                                                             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                          (coe v23))
                                                       (coe v21))
                                                    (coe v13)) in
                                       coe
                                         (let v25
                                                = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                       (coe
                                                          du_check'45'complete_2644 (coe v0)
                                                          (coe v15)
                                                          (coe
                                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                             (coe
                                                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                                (coe v16) (coe v19))
                                                             (coe
                                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                (coe v23))
                                                             (coe v21))
                                                          (coe v13))) in
                                          coe
                                            (let v26
                                                   = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                             (coe
                                                                du_check'45'complete_2644 (coe v0)
                                                                (coe v15)
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                   (coe
                                                                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                                      (coe v16) (coe v19))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                      (coe
                                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                      (coe v23))
                                                                   (coe v21))
                                                                (coe v13)))) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_withUnit'45'elim_2446
                                                  (coe v12)
                                                  (coe
                                                     (\ v27 ->
                                                        coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_curry''_506
                                                             v24)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                addInt (coe (1 :: Integer))
                                                                (coe v25))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v26) erased)))))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'cata'45'check_620 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
                      -> case coe v15 of
                           MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v18
                             -> case coe v16 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v19 v20
                                    -> coe
                                         seq (coe v20)
                                         (coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v9 v11
                                                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        du_check'45'complete_2644 (coe v0) (coe v14)
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                              (coe v18) (coe v17))
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                              (coe
                                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                              (coe v20))
                                                           (coe v17))
                                                        (coe v12))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     addInt (coe (1 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              du_check'45'complete_2644 (coe v0)
                                                              (coe v14)
                                                              (coe
                                                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                 (coe
                                                                    MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                                    (coe v18) (coe v17))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                    (coe
                                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                    (coe v20))
                                                                 (coe v17))
                                                              (coe v12)))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 du_check'45'complete_2644 (coe v0)
                                                                 (coe v14)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                    (coe
                                                                       MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                                       (coe v18) (coe v17))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                       (coe
                                                                          MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                       (coe v20))
                                                                    (coe v17))
                                                                 (coe v12)))))
                                                     erased))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'ana'45'check_640 v10 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
                      -> case coe v19 of
                           MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v20 v21
                             -> let v22
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             du_check'45'complete_2644 (coe v0) (coe v16)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v17)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46
                                                      (coe v21)))
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                   (coe v20) (coe v17)))
                                             (coe v14)) in
                                coe
                                  (let v23
                                         = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   du_check'45'complete_2644 (coe v0) (coe v16)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v17)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46
                                                            (coe v21)))
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                         (coe v20) (coe v17)))
                                                   (coe v14))) in
                                   coe
                                     (let v24
                                            = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         du_check'45'complete_2644 (coe v0)
                                                         (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                            (coe v17)
                                                            (coe
                                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                               (coe
                                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                               (coe
                                                                  MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46
                                                                  (coe v21)))
                                                            (coe
                                                               MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                               (coe v20) (coe v17)))
                                                         (coe v14)))) in
                                      coe
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v10 v13
                                              v22)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe addInt (coe (1 :: Integer)) (coe v23))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v24) erased)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'loop'45'check_652 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v12 v13 v14
                      -> let v15
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_check'45'complete_2644 (coe v0) (coe v11)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v12)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v14)
                                            (coe v12)))
                                      (coe v9)) in
                         coe
                           (let v16
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_check'45'complete_2644 (coe v0) (coe v11)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v12)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v14)
                                                  (coe v12)))
                                            (coe v9))) in
                            coe
                              (let v17
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  du_check'45'complete_2644 (coe v0) (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                     (coe v12)
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Type.C__'43'__26
                                                        (coe v14) (coe v12)))
                                                  (coe v9)))) in
                               coe
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Surface.Syntax.C_loop_548 v8 v15)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe addInt (coe (1 :: Integer)) (coe v16))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                          erased)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_664 v6 v9 v10
        -> coe du_iFromInferSub_2486 v0 v1 v6 v2 v9 v10
      MAlonzo.Code.Once.Lang.Typing.C_t'45'lam_686 v10 v13 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_check'45'complete'45'RLam_1630
                                  (coe v0) (coe v16) (coe v17) (coe v18) (coe v21) (coe v10)
                                  (coe v20) (coe v13)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'lit'45'check_702 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v15 v16
                      -> let v17
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_check'45'complete_2644 (coe v0) (coe v13) (coe v15)
                                      (coe v11)) in
                         coe
                           (let v18
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_check'45'complete_2644 (coe v0) (coe v13) (coe v15)
                                            (coe v11))) in
                            coe
                              (coe
                                 du_pair'45'lit'45'reduce_2544 (coe v9) (coe v10) (coe v17)
                                 (coe v18)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       du_check'45'complete_2644 (coe v0) (coe v14) (coe v16)
                                       (coe v12)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          du_check'45'complete_2644 (coe v0) (coe v14) (coe v16)
                                          (coe v12))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             du_check'45'complete_2644 (coe v0) (coe v14) (coe v16)
                                             (coe v12)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_712 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v12
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'In_2948
                           (coe v0) (coe v11) (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_724 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply_3150
                    (coe v0) (coe v2) (coe v11) (coe v6) (coe v2) (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2576 (coe v0) (coe v11)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'42'__24
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                (coe v2))
                             (coe v6))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2576 (coe v0) (coe v11)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                   (coe v2))
                                (coe v6))
                             (coe v9))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2576 (coe v0) (coe v11)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                      (coe v2))
                                   (coe v6))
                                (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'app'45'check_736 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v12 v13
                      -> coe
                           du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2268 (coe v0)
                           (coe v11) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'app'45'check_748 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v12 v13
                      -> coe
                           du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2316 (coe v0)
                           (coe v11) (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'app'45'check_758 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v9 v10
               -> coe
                    du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2362
                    (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate_772 v7 v8 v9 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'poly_4892
                    (coe v0) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
