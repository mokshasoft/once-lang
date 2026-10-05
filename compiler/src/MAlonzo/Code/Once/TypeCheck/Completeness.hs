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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Instance
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Completeness.Rules
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Completeness.leaf-route
d_leaf'45'route_18 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_798 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leaf'45'route_18 = erased
-- Once.TypeCheck.Completeness.app-other-route
d_app'45'other'45'route_156 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'other'45'route_156 = erased
-- Once.TypeCheck.Completeness.DPoly.⇒-parts
d_'8658''45'parts_190 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8658''45'parts_190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8658''45'parts_190
du_'8658''45'parts_190 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8658''45'parts_190
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.TypeCheck.Completeness.DPoly.arrow-parts
d_arrow'45'parts_206 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrow'45'parts_206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_arrow'45'parts_206 v7
du_arrow'45'parts_206 ::
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_arrow'45'parts_206 v0
  = coe seq (coe v0) (coe du_'8658''45'parts_190)
-- Once.TypeCheck.Completeness.DPoly.gp-eq
d_gp'45'eq_238 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gp'45'eq_238 = erased
-- Once.TypeCheck.Completeness.DPoly.gg-eq
d_gg'45'eq_276 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gg'45'eq_276 = erased
-- Once.TypeCheck.Completeness.DPoly.gm-eq
d_gm'45'eq_334 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gm'45'eq_334 = erased
-- Once.TypeCheck.Completeness.DPoly.at-π
d_at'45'π_406 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at'45'π_406 v0 v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
              ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22
  = du_at'45'π_406 v0 v1 v2 v3 v6 v7 v9 v18
du_at'45'π_406 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at'45'π_406 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__22
              (coe v4) (coe v3) in
    coe
      (case coe v8 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
           -> if coe v9
                then case coe v10 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                         -> let v12
                                  = MAlonzo.Code.Once.Type.Match.d_instantiateAcc_102
                                      (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v2)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                                         (coe
                                            MAlonzo.Code.Once.Type.d_substPoly_562 (coe v7)
                                            (coe v6)))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                            coe
                              (case coe v12 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                   -> let v14
                                            = MAlonzo.Code.Once.Type.Instance.d_θof_478 (coe v13) in
                                      coe
                                        (let v15
                                               = MAlonzo.Code.Once.Type.Rigid.d_allBase'63'_594
                                                   (coe v14)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.Rigid.d_ftvK_6
                                                      (coe v5)) in
                                         coe
                                           (case coe v15 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                -> if coe v16
                                                     then coe
                                                            seq (coe v17)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe
                                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                     (coe v2)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                        (coe v4))
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.d_substPoly_562
                                                                        (coe v7) (coe v6)))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                                                                     (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170
                                                                        (coe v2))
                                                                     (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.d_substPoly_562
                                                                           (coe v7) (coe v6)))
                                                                     v11)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Syntax.C_poly_398
                                                                     v1))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe (0 :: Integer))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                                                        (coe v0))
                                                                     erased)))
                                                     else (let v18
                                                                 = seq
                                                                     (coe v17)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                        (coe v16)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                           coe
                                                             (case coe v18 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                  -> if coe v19
                                                                       then coe
                                                                              seq (coe v20)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                                       (coe v2)
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Type.C_Many_10)
                                                                                          (coe v4))
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Type.d_substPoly_562
                                                                                          (coe v7)
                                                                                          (coe v6)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                                                                                       (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170
                                                                                          (coe v2))
                                                                                       (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Type.d_substPoly_562
                                                                                             (coe
                                                                                                v7)
                                                                                             (coe
                                                                                                v6)))
                                                                                       v11)
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_poly_398
                                                                                       v1))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       (0 ::
                                                                                          Integer))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                                                                          (coe v0))
                                                                                       erased)))
                                                                       else coe
                                                                              seq (coe v20)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v10) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.DPoly.at-m
d_at'45'm_650 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at'45'm_650 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
              ~v14 ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21
  = du_at'45'm_650 v0 v1 v2 v3 v6 v7 v8 v9 v16 v18
du_at'45'm_650 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at'45'm_650 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_at'45'π_406 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v5) (coe v7)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Once.Type.Instance.du_instantiate'45'sound_1596
                  (coe v6) (coe v2)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                     (coe
                        MAlonzo.Code.Once.Type.Instance.du_instantiate'45'complete_432
                        (coe v6)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe du_arrow'45'parts_206 (coe v8))))))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_at'45'π_406 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v5) (coe v7)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                     (coe
                        MAlonzo.Code.Once.Type.Instance.du_instantiate'45'sound_1596
                        (coe v6) (coe v2)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Once.Type.Instance.du_instantiate'45'complete_432
                              (coe v6)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe du_arrow'45'parts_206 (coe v8)))))))))))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        du_at'45'π_406 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe v7)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Once.Type.Instance.du_instantiate'45'sound_1596
                              (coe v6) (coe v2)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.Type.Instance.du_instantiate'45'complete_432
                                    (coe v6)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe du_arrow'45'parts_206 (coe v8))))))))))))
            erased))
-- Once.TypeCheck.Completeness.DPoly.from-arrow
d_from'45'arrow_758 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_from'45'arrow_758 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11
                    ~v12 ~v13 ~v14 ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21
  = du_from'45'arrow_758 v0 v1 v2 v3 v8 v9 v16 v18
du_from'45'arrow_758 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_from'45'arrow_758 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Once.Type.C_as'45'pure_674
        -> let v10
                 = coe
                     MAlonzo.Code.Data.List.Relation.Binary.Subset.DecSetoid.du__'8838''63'__40
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                        (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
                     (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v5))
                     (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v4)) in
           coe
             (case coe v10 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                  -> if coe v11
                       then coe
                              seq (coe v12)
                              (coe
                                 du_at'45'm_650 (coe v0) (coe v1) (coe v2) (coe v3)
                                 (coe MAlonzo.Code.Once.Type.C_pure_34)
                                 (coe
                                    MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 (coe v4)
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                                 (coe v4) (coe v5) (coe MAlonzo.Code.Once.Type.C_as'45'pure_674)
                                 (coe v7))
                       else coe
                              seq (coe v12) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Type.C_as'45'eff_680
        -> let v10
                 = coe
                     MAlonzo.Code.Data.List.Relation.Binary.Subset.DecSetoid.du__'8838''63'__40
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                        (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
                     (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v5))
                     (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v4)) in
           coe
             (case coe v10 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                  -> if coe v11
                       then coe
                              seq (coe v12)
                              (coe
                                 du_at'45'm_650 (coe v0) (coe v1) (coe v2) (coe v3)
                                 (coe MAlonzo.Code.Once.Type.C_eff_36)
                                 (coe MAlonzo.Code.Once.Type.C_PEff_274 (coe v4) (coe v5)) (coe v4)
                                 (coe v5) (coe MAlonzo.Code.Once.Type.C_as'45'eff_680) (coe v7))
                       else coe
                              seq (coe v12) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.DPoly.from-lookups
d_from'45'lookups_1018 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_from'45'lookups_1018 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11
                       ~v12 ~v13 ~v14 ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21
  = du_from'45'lookups_1018 v0 v1 v2 v3 v8 v9 v16 v18
du_from'45'lookups_1018 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_from'45'lookups_1018 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_from'45'arrow_758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v5) (coe v6) (coe v7)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_from'45'arrow_758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v5) (coe v6) (coe v7))))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        du_from'45'arrow_758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe v6) (coe v7)))))
            erased))
-- Once.TypeCheck.Completeness.poly-head-fails
d_poly'45'head'45'fails_1072 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'head'45'fails_1072 = erased
-- Once.TypeCheck.Completeness.var-route
d_var'45'route_1108 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_var'45'route_1108 = erased
-- Once.TypeCheck.Completeness.given-infer-route
d_given'45'infer'45'route_1144 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_given'45'infer'45'route_1144 = erased
-- Once.TypeCheck.Completeness.given-infer-complete
d_given'45'infer'45'complete_1348 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'infer'45'complete_1348 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8
                                  ~v9 ~v10 v11 ~v12 ~v13 ~v14
  = du_given'45'infer'45'complete_1348 v2 v3 v4 v5 v6 v11
du_given'45'infer'45'complete_1348 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'infer'45'complete_1348 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
               -> let v13
                        = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                            (coe v0) (coe v1) in
                  coe
                    (let v14
                           = MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__22
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
                                                                       MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                          (coe v1)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.C_Many_10)
                                                                             (coe v4))
                                                                          (coe v2))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                                                                          v17
                                                                          (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170
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
d_given'45'cata'45'complete_1434 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'cata'45'complete_1434 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
                                 ~v9 v10 ~v11
  = du_given'45'cata'45'complete_1434 v2 v3 v4 v5 v10
du_given'45'cata'45'complete_1434 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'cata'45'complete_1434 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
               -> let v12
                        = coe
                            MAlonzo.Code.Once.Type.DecEq.du_'8799'T'45''8658''45'aux_116
                            (coe
                               MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
                               (coe
                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v0) (coe v1))
                               (coe
                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v0) (coe v1)))
                            (coe
                               MAlonzo.Code.Once.Type.du_'8799'k'45'aux_82
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                               (coe MAlonzo.Code.Once.Type.d__'8799'p__72 (coe v2) (coe v2)))
                            (coe
                               MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v1) (coe v1)) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                         -> if coe v13
                              then coe
                                     seq (coe v14)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_516 v3 v9)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe addInt (coe (1 :: Integer)) (coe v10))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                              erased)))
                              else coe
                                     seq (coe v14)
                                     (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.compose-f-complete
d_compose'45'f'45'complete_1506 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compose'45'f'45'complete_1506 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10
                                ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_compose'45'f'45'complete_1506 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_compose'45'f'45'complete_1506 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compose'45'f'45'complete_1506 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = let v9
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
              (coe v0) (coe v1) in
    coe
      (case coe v9 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
           -> case coe v10 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v12 v13 v14 v15 v16
                  -> let v17
                           = coe
                               MAlonzo.Code.Once.Type.Sub.du_arr'45'aux_260
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                               (coe
                                  MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392 (coe v4) (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392 (coe v6) (coe v5))
                               (coe
                                  MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__22 (coe v8)
                                  (coe v7)) in
                     coe
                       (case coe v17 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                            -> if coe v18
                                 then case coe v19 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                          -> let v21
                                                   = coe
                                                       MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
                                                       (coe v0) (coe v2)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                          (coe v3)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                             (coe MAlonzo.Code.Once.Type.C_Many_10)
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
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_comp''_448
                                                                   v13 v24 v4
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                         (coe v4)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_Many_10)
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
d_compose'45'g'45'complete_1684 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compose'45'g'45'complete_1684 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10
                                ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
  = du_compose'45'g'45'complete_1684 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_compose'45'g'45'complete_1684 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compose'45'g'45'complete_1684 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_258 v12 v13 v14 v15 v16
               -> let v17
                        = coe
                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
                            (coe v0) (coe v1)
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v12)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
                               (coe v5)) in
                  coe
                    (case coe v17 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                         -> case coe v18 of
                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v20 v21 v22 v23
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_comp''_448 v20 v13 v12
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
                                     du_compose'45'f'45'complete_1506 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_260 v12
               -> coe
                    du_compose'45'f'45'complete_1506 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.infer-complete-RApp-spine
d_infer'45'complete'45'RApp'45'spine_1934 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
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
d_infer'45'complete'45'RApp'45'spine_1934 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                          ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_infer'45'complete'45'RApp'45'spine_1934 v0 v1 v2
du_infer'45'complete'45'RApp'45'spine_1934 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'spine_1934 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe
                seq (coe v4)
                (let v6
                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
                           (coe v0) (coe v2) in
                 coe
                   (case coe v6 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                        -> case coe v7 of
                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v9 v10 v11 v12 v13
                               -> let v14
                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6008
                                            (coe v0) (coe v1) (coe v9)
                                            (coe MAlonzo.Code.Once.Type.C_pure_34) in
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
                                                        (coe MAlonzo.Code.Once.Type.C_Many_10) v19
                                                        v11)
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
d_checkElab'45'fallback'45'RVar_2050 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar_2050 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                     ~v8 ~v9
  = du_checkElab'45'fallback'45'RVar_2050 v0 v1 v2 v3
du_checkElab'45'fallback'45'RVar_2050 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar_2050 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_4702
              (coe v0) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_496
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0))
                 (coe v2)
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_394 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0)))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
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
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v3
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
d_completeness'45'gap'45'inl'45'app'45'check'45'eq_2132 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'inl'45'app'45'check'45'eq_2132 v0 v1 v2
                                                        ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2132 v0 v1 v2
du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2132 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2132 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v6 v2
                          (coe MAlonzo.Code.Once.IR.C_inl_54) v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.completeness-gap-inr-app-check-eq
d_completeness'45'gap'45'inr'45'app'45'check'45'eq_2180 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'inr'45'app'45'check'45'eq_2180 v0 v1 ~v2
                                                        v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2180 v0 v1 v3
du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2180 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2180 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v6 v2
                          (coe MAlonzo.Code.Once.IR.C_inr_60) v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.completeness-gap-initial-app-check-eq
d_completeness'45'gap'45'initial'45'app'45'check'45'eq_2226 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'initial'45'app'45'check'45'eq_2226 v0 v1
                                                            ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2226
      v0 v1
du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2226 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2226 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
              (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Void_122) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v5
                          (coe MAlonzo.Code.Once.Type.C_Void_122)
                          (coe MAlonzo.Code.Once.IR.C_initial_76) v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v7))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.checkElabV-RResolved-J
d_checkElabV'45'RResolved'45'J_2256 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_1170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkElabV'45'RResolved'45'J_2256 = erased
-- Once.TypeCheck.Completeness.caseGo-success
d_caseGo'45'success_2302 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caseGo'45'success_2302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 v13 v14 v15 ~v16 ~v17 ~v18
  = du_caseGo'45'success_2302 v13 v14 v15
du_caseGo'45'success_2302 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caseGo'45'success_2302 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v0) (coe v2)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased)
-- Once.TypeCheck.Completeness.check-completeV
d_check'45'completeV_2332 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'completeV_2332 v0 v1 v2 ~v3 v4
  = du_check'45'completeV_2332 v0 v1 v2 v4
du_check'45'completeV_2332 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'completeV_2332 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
              (coe v0) (coe v1) (coe v2) in
    coe
      (let v5
             = coe
                 du_check'45'complete_2508 (coe v0) (coe v1) (coe v2) (coe v3) in
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
d_iFromInferSub_2350 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_iFromInferSub_2350 v0 v1 v2 v3 ~v4 v5
  = du_iFromInferSub_2350 v0 v1 v2 v3 v5
du_iFromInferSub_2350 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_iFromInferSub_2350 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v7
               -> coe
                    (\ v8 ->
                       seq
                         (coe v8)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RInt_16
                            (coe v0) (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v10 v11 v12 v13
               -> coe
                    (\ v14 ->
                       seq
                         (coe v14)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RFloat_52
                            (coe v0) (coe v10) (coe v11) (coe v12)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_46
        -> coe
             (\ v6 ->
                seq
                  (coe v6)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RUnit_98
                     (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_50
        -> coe
             (\ v6 ->
                seq
                  (coe v6)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RVar'45'unit_2402
                     (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_62 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    (\ v12 ->
                       coe
                         du_checkElab'45'fallback'45'RVar_2050 (coe v0) (coe v3) (coe v11)
                         (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_72 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RQualified_136
                         (coe v0) (coe v3) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_80 v8 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RResolved_324
                         (coe v0) (coe v3) (coe v11) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_88 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v12
               -> coe
                    (\ v13 ->
                       coe
                         du_checkElab'45'fallback'45'RVar_2050 (coe v0) (coe v3) (coe v12)
                         (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_104 v8 v9 v10 v11 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v17
               -> coe
                    (\ v18 ->
                       coe
                         du_checkElab'45'fallback'45'RVar_2050 (coe v0) (coe v3) (coe v17)
                         (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_114 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RAnnot_1174
                         (coe v0) (coe v3) (coe v11) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_130 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v16 v17
                      -> coe
                           (\ v18 ->
                              case coe v18 of
                                MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84 v23 v24
                                  -> case coe v3 of
                                       MAlonzo.Code.Once.Type.C__'42'__124 v25 v26
                                         -> let v27
                                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         du_iFromInferSub_2350 v0 v14 v16 v25 v12
                                                         v23) in
                                            coe
                                              (let v28
                                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               du_iFromInferSub_2350 v0 v14 v16 v25
                                                               v12 v23)) in
                                               coe
                                                 (coe
                                                    du_pair'45'lit'45'reduce_2408 (coe v10)
                                                    (coe v11) (coe v27) (coe v28)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                       (coe
                                                          du_iFromInferSub_2350 v0 v15 v17 v26 v13
                                                          v24))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             du_iFromInferSub_2350 v0 v15 v17 v26
                                                             v13 v24)))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                             (coe
                                                                du_iFromInferSub_2350 v0 v15 v17 v26
                                                                v13 v24))))))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_138 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> coe
                    (\ v11 ->
                       seq
                         (coe v11)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RUnaryOp_1792
                            (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Int_134)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_150
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v11
               -> coe
                    (\ v12 ->
                       seq
                         (coe v12)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RUnaryOp_1792
                            (coe v0) (coe v11) (coe MAlonzo.Code.Once.Type.C_Float_136)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_170 v9 v11 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v16 v17 v18
               -> coe
                    (\ v19 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RLet_1352
                         (coe v0) (coe v3) (coe v16) (coe v17) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_200 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v22 v23 v24 v25 v26
               -> coe
                    (\ v27 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RDestruct_1562
                         (coe v0) (coe v3) (coe v22) (coe v23) (coe v24) (coe v25)
                         (coe v26))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5836
                         (coe v0) (coe v3) (coe v14) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_228 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5836
                         (coe v0) (coe v3) (coe v14) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_242 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5836
                         (coe v0) (coe v3) (coe v14) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_256 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5836
                         (coe v0) (coe v3) (coe v14) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5836
                         (coe v0) (coe v3) (coe v14) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_280 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'id_4890
                         (coe v0) (coe v3) (coe v11) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_292 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'fst_4978
                         (coe v0) (coe v3) (coe v12) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_304 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'snd_5066
                         (coe v0) (coe v3) (coe v12) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_314 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'terminal_5656
                         (coe v0) (coe v3) (coe v11)
                         (coe MAlonzo.Code.Once.Type.C_Unit_120))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_326 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply_3134
                         (coe v0) (coe v3) (coe v12) (coe v7) (coe v2) (coe v9)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               du_infer'45'complete_2440 (coe v0) (coe v12)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'42'__124
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                                     (coe v2))
                                  (coe v7))
                               (coe v10)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  du_infer'45'complete_2440 (coe v0) (coe v12)
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'42'__124
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                           (coe MAlonzo.Code.Once.Type.C_pure_34))
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
                                     du_infer'45'complete_2440 (coe v0) (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'42'__124
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                                           (coe v2))
                                        (coe v7))
                                     (coe v10))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_338 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
                      -> coe
                           (\ v16 ->
                              coe
                                MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3210
                                (coe v0) (coe v3) (coe v12) (coe v7) (coe v15) (coe v9)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_infer'45'complete_2440 (coe v0) (coe v12)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'42'__124
                                         (coe
                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                               (coe MAlonzo.Code.Once.Type.C_Many_10)
                                               (coe MAlonzo.Code.Once.Type.C_eff_36))
                                            (coe v15))
                                         (coe v7))
                                      (coe v10)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         du_infer'45'complete_2440 (coe v0) (coe v12)
                                         (coe
                                            MAlonzo.Code.Once.Type.C__'42'__124
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v7)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_eff_36))
                                               (coe v15))
                                            (coe v7))
                                         (coe v10))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_infer'45'complete_2440 (coe v0) (coe v12)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'42'__124
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe MAlonzo.Code.Once.Type.C_eff_36))
                                                  (coe v15))
                                               (coe v7))
                                            (coe v10))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_350 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    (\ v15 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'Out_5744
                         (coe v0) (coe v3) (coe v14)
                         (coe
                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v7)
                            (coe
                               MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v7)
                               (coe MAlonzo.Code.Once.Type.C_pure_34))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_362 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    (\ v15 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'Out_5744
                         (coe v0) (coe v3) (coe v14)
                         (coe
                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                            (coe MAlonzo.Code.Once.Type.C_Unit_120)
                            (coe
                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                               (coe MAlonzo.Code.Once.Type.C_Many_10)
                               (coe MAlonzo.Code.Once.Type.C_eff_36))
                            (coe
                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v7)
                               (coe
                                  MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v7)
                                  (coe MAlonzo.Code.Once.Type.C_eff_36)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_380 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    (\ v18 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic_5170
                         (coe v0) (coe v3) (coe v16) (coe v17) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_396 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
                      -> coe
                           (\ v20 ->
                              coe
                                MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic_5170
                                (coe v0) (coe v3) (coe v15) (coe v16)
                                (coe
                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                   (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                   (coe
                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                      (coe MAlonzo.Code.Once.Type.C_eff_36))
                                   (coe v19)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_412 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic_5170
                         (coe v0) (coe v3) (coe v15) (coe v16) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.check-completeV-from-infer
d_check'45'completeV'45'from'45'infer_2370 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'completeV'45'from'45'infer_2370 v0 v1 v2 v3 ~v4 v5 v6
  = du_check'45'completeV'45'from'45'infer_2370 v0 v1 v2 v3 v5 v6
du_check'45'completeV'45'from'45'infer_2370 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'completeV'45'from'45'infer_2370 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
              (coe v0) (coe v1) (coe v3) in
    coe
      (let v7 = coe du_iFromInferSub_2350 v0 v1 v2 v3 v4 v5 in
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
d_pair'45'lit'45'reduce_2408 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair'45'lit'45'reduce_2408 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9
                             ~v10 v11 v12 v13 ~v14 ~v15 ~v16
  = du_pair'45'lit'45'reduce_2408 v5 v6 v7 v8 v11 v12 v13
du_pair'45'lit'45'reduce_2408 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair'45'lit'45'reduce_2408 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v0 v1 v2 v4)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) erased))
-- Once.TypeCheck.Completeness.iFromInfer
d_iFromInfer_2424 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_iFromInfer_2424 v0 v1 v2 ~v3 v4 = du_iFromInfer_2424 v0 v1 v2 v4
du_iFromInfer_2424 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_iFromInfer_2424 v0 v1 v2 v3
  = coe
      du_iFromInferSub_2350 v0 v1 v2 v2 v3
      (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v2))
-- Once.TypeCheck.Completeness.infer-complete
d_infer'45'complete_2440 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete_2440 v0 v1 v2 ~v3 v4
  = du_infer'45'complete_2440 v0 v1 v2 v4
du_infer'45'complete_2440 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete_2440 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.d_infer'45'complete'45'RInt_18
                    (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_float_194
                       (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
                          (coe v9) (coe v10) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                          erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_46
        -> coe
             MAlonzo.Code.Once.TypeCheck.Completeness.Rules.d_infer'45'complete'45'RUnit_30
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_50
        -> coe
             MAlonzo.Code.Once.TypeCheck.Completeness.Rules.d_infer'45'complete'45'RVar'45'unit_40
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_62 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RVar'45'local_1030
             (coe v0) (coe v8)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_72 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RQualified_56
                    (coe v0) (coe v10) (coe v11) (coe v2) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_80 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RResolved_202
                    (coe v0) (coe v10) (coe v2) (coe v7) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_88 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RVar'45'import_1070
                    (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_104 v7 v8 v9 v10 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'poly'45'infer_4850
                    (coe v0) (coe v16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_114 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RAnnot_552
                    (coe v0) (coe v10) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_130 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RPair_424
                    (coe v0) (coe v13) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_138 v7
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v9
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RUnaryOp'45'neg_482
                    (coe v0) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_150
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v11 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_float_194
                              (MAlonzo.Code.Once.Float.Decimal.d_negate_22
                                 (coe
                                    MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v11)
                                    (coe v12) (coe v13))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                    (coe v0))
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_170 v8 v10 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RLet_614
                    (coe v0) (coe v15) (coe v16) (coe v17)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_200 v10 v11 v13 v14 v15 v16 v17 v18 v19 v20
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v21 v22 v23 v24 v25
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RDestruct_1792
                    (coe v0) (coe v21) (coe v22) (coe v23) (coe v24) (coe v25) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RBinOp'45'arith_1512
                    (coe v0) (coe v13) (coe v14) (coe v15) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v14)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v14)
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v15)
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2440 (coe v0) (coe v15)
                                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_228 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RBinOp'45'arith'45'float_1406
                    (coe v0) (coe v13) (coe v14) (coe v15) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v14)
                          (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v12)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v14)
                             (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v15)
                             (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v12))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2440 (coe v0) (coe v15)
                                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_242 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1202
                    (coe v0) (coe v13) (coe v14) (coe v15) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v14)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v12)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v14)
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v15)
                             (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v12))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2440 (coe v0) (coe v15)
                                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_256 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1304
                    (coe v0) (coe v13) (coe v14) (coe v15) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v14)
                          (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v14)
                             (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v15)
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2440 (coe v0) (coe v15)
                                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RBinOp'45'cmp_1622
                    (coe v0) (coe v13) (coe v14) (coe v15) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v14)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v14)
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v15)
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2440 (coe v0) (coe v15)
                                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_280 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'id_686
                    (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_292 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'fst_888
                    (coe v0) (coe v11) (coe v2) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v11)
                          (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v2) (coe v7))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v11)
                             (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v2) (coe v7))
                             (coe v9))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2440 (coe v0) (coe v11)
                                (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v2) (coe v7))
                                (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_304 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'snd_920
                    (coe v0) (coe v11) (coe v6) (coe v2) (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v11)
                          (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v6) (coe v2))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v11)
                             (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v6) (coe v2))
                             (coe v9))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_infer'45'complete_2440 (coe v0) (coe v11)
                                (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v6) (coe v2))
                                (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_314 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'terminal_724
                    (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_326 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'apply_952
                    (coe v0) (coe v11) (coe v6) (coe v2) (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v11)
                          (coe
                             MAlonzo.Code.Once.Type.C__'42'__124
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v6)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                (coe v2))
                             (coe v6))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v11)
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe
                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v6)
                                   (coe
                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                      (coe MAlonzo.Code.Once.Type.C_pure_34))
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
                                du_infer'45'complete_2440 (coe v0) (coe v11)
                                (coe
                                   MAlonzo.Code.Once.Type.C__'42'__124
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v6)
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                                      (coe v2))
                                   (coe v6))
                                (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_338 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'apply'45'eff_994
                           (coe v0) (coe v11) (coe v6) (coe v14) (coe v8)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 du_infer'45'complete_2440 (coe v0) (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'42'__124
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v6)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                                       (coe v14))
                                    (coe v6))
                                 (coe v9)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    du_infer'45'complete_2440 (coe v0) (coe v11)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'42'__124
                                       (coe
                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v6)
                                          (coe
                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                                          (coe v14))
                                       (coe v6))
                                    (coe v9))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       du_infer'45'complete_2440 (coe v0) (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.Type.C__'42'__124
                                          (coe
                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v6)
                                             (coe
                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                (coe MAlonzo.Code.Once.Type.C_eff_36))
                                             (coe v14))
                                          (coe v6))
                                       (coe v9)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_350 v6 v8 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'Out_764
                    (coe v0) (coe v13) (coe v6) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_362 v6 v8 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'Out'45'eff_826
                    (coe v0) (coe v13) (coe v6) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_380 v7 v9 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'generic_1990
                    (coe v0) (coe v15) (coe v16) (coe v7) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_396 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'eff_2118
                    (coe v0) (coe v14) (coe v15) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_412 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    du_spine'45'complete_2462 (coe v0) (coe v14) (coe v15) (coe v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.spine-complete
d_spine'45'complete_2462 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spine'45'complete_2462 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_spine'45'complete_2462 v0 v1 v2 v9
du_spine'45'complete_2462 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spine'45'complete_2462 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_744 v7 v10 v12 v13 v14
        -> coe
             seq (coe v14)
             (coe
                MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_infer'45'complete'45'RApp'45'generic_1990
                (coe v0) (coe v1) (coe v2) (coe v7)
                (coe MAlonzo.Code.Once.Type.C_Many_10))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_768 v9 v10 v11 v12 v13 v14 v19 v20 v21 v22
        -> coe
             du_infer'45'complete'45'RApp'45'spine_1934 (coe v0) (coe v1)
             (coe v2)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_786 v9 v13
        -> coe
             du_infer'45'complete'45'RApp'45'spine_1934 (coe v0) (coe v1)
             (coe v2)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_806 v8 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> coe
                           du_infer'45'complete'45'RApp'45'spine_1934 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                    (coe
                                       MAlonzo.Code.Once.CanonicalName.C_canonical_10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_868 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> coe
                           du_infer'45'complete'45'RApp'45'spine_1934 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                    (coe
                                       MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe ("Generators" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe ("case" :: Data.Text.Text))
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                 (coe v18))
                              (coe v16))
                           (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_888 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> coe
                           du_infer'45'complete'45'RApp'45'spine_1934 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                    (coe
                                       MAlonzo.Code.Once.CanonicalName.C_canonical_10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_902 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    du_infer'45'complete'45'RApp'45'spine_1934 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                          (coe
                             MAlonzo.Code.Once.CanonicalName.C_canonical_10
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe ("Generators" :: Data.Text.Text))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("cata" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v13))
                    (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.given-complete
d_given'45'complete_2482 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'complete_2482 v0 v1 v2 v3 v4 ~v5 v6
  = du_given'45'complete_2482 v0 v1 v2 v3 v4 v6
du_given'45'complete_2482 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'complete_2482 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_744 v9 v12 v14 v15 v16
        -> coe
             du_given'45'infer'45'complete_1348 (coe v2) (coe v9) (coe v3)
             (coe v4) (coe v12)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_768 v11 v12 v13 v14 v15 v16 v21 v22 v23 v24
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v25
               -> case coe v23 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                      -> coe
                           seq (coe v27)
                           (coe
                              du_from'45'lookups_1018 (coe v0) (coe v25) (coe v2) (coe v4)
                              (coe v13) (coe v14) (coe v21) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_786 v11 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v16 v17
               -> let v18
                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
                            (coe
                               MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                               (coe v16) (coe v2))
                            (coe v17) in
                  coe
                    (let v19
                           = coe
                               du_infer'45'complete_2440
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                                  (coe v16) (coe v2))
                               (coe v17) (coe v3) (coe v15) in
                     coe
                       (case coe v18 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                            -> case coe v20 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v22 v23 v24 v25 v26
                                   -> case coe v23 of
                                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v28 v29
                                          -> case coe v19 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                 -> case coe v31 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                        -> coe
                                                             seq (coe v33)
                                                             (let v34
                                                                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1252
                                                                        (coe v28)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10) in
                                                              coe
                                                                (let v35
                                                                       = coe
                                                                           MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_decideLeq'45'just_1644
                                                                           (coe v28)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C_Many_10) in
                                                                 coe
                                                                   (coe
                                                                      seq (coe v34)
                                                                      (coe
                                                                         seq (coe v35)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe
                                                                               MAlonzo.Code.Once.Surface.Syntax.C_lam_34
                                                                               v28 v24)
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe
                                                                                  addInt
                                                                                  (coe
                                                                                     (1 :: Integer))
                                                                                  (coe v25))
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe v26)
                                                                                  erased)))))))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_806 v10 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> let v21
                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6008
                                   (coe v0) (coe v18) (coe v2) (coe v4) in
                         coe
                           (let v22
                                  = coe
                                      du_given'45'complete_2482 (coe v0) (coe v18) (coe v2)
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
                                                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6008
                                                                            (coe v0) (coe v20)
                                                                            (coe v25) (coe v4) in
                                                                  coe
                                                                    (let v37
                                                                           = coe
                                                                               du_given'45'complete_2482
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
                                                                                                            MAlonzo.Code.Once.Surface.Syntax.C_comp''_448
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_814
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                (coe MAlonzo.Code.Once.IR.C_id_20))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                   erased))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_824
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                (coe MAlonzo.Code.Once.IR.C_fst_42))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                   erased))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_834
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                (coe MAlonzo.Code.Once.IR.C_snd_48))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                   erased))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_842
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                (coe MAlonzo.Code.Once.IR.C_terminal_72))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                   erased))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_848
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                (coe MAlonzo.Code.Once.IR.C_initial_76))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                   erased))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_868 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'43'__126 v21 v22
                             -> let v23
                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6008
                                          (coe v0) (coe v20) (coe v21) (coe v4) in
                                coe
                                  (let v24
                                         = coe
                                             du_given'45'complete_2482 (coe v0) (coe v20) (coe v21)
                                             (coe v3) (coe v4) (coe v15) in
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
                                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6008
                                                                                   (coe v0)
                                                                                   (coe v18)
                                                                                   (coe v22)
                                                                                   (coe v4) in
                                                                         coe
                                                                           (let v39
                                                                                  = coe
                                                                                      du_given'45'complete_2482
                                                                                      (coe v0)
                                                                                      (coe v18)
                                                                                      (coe v22)
                                                                                      (coe v27)
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
                                                                                                             (let v51
                                                                                                                    = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
                                                                                                                        (coe
                                                                                                                           v27)
                                                                                                                        (coe
                                                                                                                           v27) in
                                                                                                              coe
                                                                                                                (case coe
                                                                                                                        v51 of
                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v52 v53
                                                                                                                     -> if coe
                                                                                                                             v52
                                                                                                                          then coe
                                                                                                                                 seq
                                                                                                                                 (coe
                                                                                                                                    v53)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_copair''_466
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
                                                                                                                          else coe
                                                                                                                                 seq
                                                                                                                                 (coe
                                                                                                                                    v53)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_888 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'42'__124 v21 v22
                             -> let v23
                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6008
                                          (coe v0) (coe v20) (coe v2) (coe v4) in
                                coe
                                  (let v24
                                         = coe
                                             du_given'45'complete_2482 (coe v0) (coe v20) (coe v2)
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
                                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6008
                                                                                   (coe v0)
                                                                                   (coe v18)
                                                                                   (coe v2)
                                                                                   (coe v4) in
                                                                         coe
                                                                           (let v39
                                                                                  = coe
                                                                                      du_given'45'complete_2482
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
                                                                                                                   MAlonzo.Code.Once.Surface.Syntax.C_fork''_484
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_902 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v16
                      -> coe
                           du_given'45'cata'45'complete_1434 (coe v16) (coe v3) (coe v4)
                           (coe v12)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                              (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.nothing≢just
d_nothing'8802'just_2492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_nothing'8802'just_2492 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_nothing'8802'just_2492
du_nothing'8802'just_2492 :: AgdaAny
du_nothing'8802'just_2492 = MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.check-complete
d_check'45'complete_2508 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete_2508 v0 v1 v2 ~v3 v4
  = du_check'45'complete_2508 v0 v1 v2 v4
du_check'45'complete_2508 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete_2508 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_420
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v7 v8 v9
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'id_2634
                    (coe v0) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_430
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v11 v12
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'fst_2674
                           (coe v0) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_440
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v11 v12
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'snd_2714
                           (coe v0) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_448
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'terminal_2752
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_456
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'initial_2790
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_466
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'inl_2810
                    (coe v0) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_476
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'inr_2850
                    (coe v0) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_496 v8 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                                    -> let v24
                                             = MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6008
                                                 (coe v0) (coe v16) (coe v19) (coe v23) in
                                       coe
                                         (let v25
                                                = coe
                                                    du_given'45'complete_2482 (coe v0) (coe v16)
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
                                                                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
                                                                                          (coe v0)
                                                                                          (coe v18)
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                                             (coe
                                                                                                v28)
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                (coe
                                                                                                   v23))
                                                                                             (coe
                                                                                                v21)) in
                                                                                coe
                                                                                  (let v40
                                                                                         = coe
                                                                                             du_check'45'complete_2508
                                                                                             (coe
                                                                                                v0)
                                                                                             (coe
                                                                                                v18)
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                                                (coe
                                                                                                   v28)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.C_Many_10)
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
                                                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_comp''_448
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_520 v8 v10 v12 v13 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v22 v23 v24
                             -> case coe v23 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                                    -> coe
                                         du_compose'45'g'45'complete_1684 (coe v0) (coe v21)
                                         (coe v19) (coe v22) (coe v8) (coe v24) (coe v10) (coe v26)
                                         (coe v12)
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.d_elabGivenV_6008
                                            (coe v0) (coe v19) (coe v22) (coe v26))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_540 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
                             -> case coe v19 of
                                  MAlonzo.Code.Once.Type.C__'43'__126 v22 v23
                                    -> case coe v20 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v24 v25
                                           -> case coe v25 of
                                                MAlonzo.Code.Once.Type.C_pure_34
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Once.Surface.Syntax.C_copair''_466
                                                          v11 v12
                                                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                du_check'45'completeV_2332 (coe v0)
                                                                (coe v18)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                   (coe v22)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                      (coe v25))
                                                                   (coe v21))
                                                                (coe v13)))
                                                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                du_check'45'completeV_2332 (coe v0)
                                                                (coe v16)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                   (coe v23)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                      (coe v25))
                                                                   (coe v21))
                                                                (coe v14))))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                du_caseGo'45'success_2302
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                      (coe
                                                                         du_check'45'completeV_2332
                                                                         (coe v0) (coe v18)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                            (coe v22)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
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
                                                                            du_check'45'completeV_2332
                                                                            (coe v0) (coe v18)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                               (coe v22)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                                  (coe v25))
                                                                               (coe v21))
                                                                            (coe v13)))))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                      (coe
                                                                         du_check'45'completeV_2332
                                                                         (coe v0) (coe v16)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                            (coe v23)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
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
                                                                      du_caseGo'45'success_2302
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                            (coe
                                                                               du_check'45'completeV_2332
                                                                               (coe v0) (coe v18)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                                  (coe v22)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.C_Many_10)
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
                                                                                  du_check'45'completeV_2332
                                                                                  (coe v0) (coe v18)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                                     (coe v22)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                                        (coe v25))
                                                                                     (coe v21))
                                                                                  (coe v13)))))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                            (coe
                                                                               du_check'45'completeV_2332
                                                                               (coe v0) (coe v16)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                                  (coe v23)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.C_Many_10)
                                                                                     (coe v25))
                                                                                  (coe v21))
                                                                               (coe v14)))))))
                                                             erased))
                                                MAlonzo.Code.Once.Type.C_eff_36
                                                  -> let v26
                                                           = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  du_check'45'complete_2508 (coe v0)
                                                                  (coe v18)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                     (coe v22)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                        (coe v25))
                                                                     (coe v21))
                                                                  (coe v13)) in
                                                     coe
                                                       (let v27
                                                              = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        du_check'45'complete_2508
                                                                        (coe v0) (coe v18)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                           (coe v22)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C_Many_10)
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
                                                                              du_check'45'complete_2508
                                                                              (coe v0) (coe v18)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                                 (coe v22)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Type.C_Many_10)
                                                                                    (coe v25))
                                                                                 (coe v21))
                                                                              (coe v13)))) in
                                                           coe
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_copair''_466
                                                                   v11 v12 v26
                                                                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                      (coe
                                                                         du_check'45'complete_2508
                                                                         (coe v0) (coe v16)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                            (coe v23)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
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
                                                                                  du_check'45'complete_2508
                                                                                  (coe v0) (coe v16)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                                     (coe v23)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Type.C_Many_10)
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_560 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                                    -> case coe v21 of
                                         MAlonzo.Code.Once.Type.C__'42'__124 v24 v25
                                           -> let v26
                                                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           du_check'45'complete_2508 (coe v0)
                                                           (coe v18)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                              (coe v19)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                 (coe v23))
                                                              (coe v24))
                                                           (coe v13)) in
                                              coe
                                                (let v27
                                                       = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 du_check'45'complete_2508 (coe v0)
                                                                 (coe v18)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                    (coe v19)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C_Many_10)
                                                                       (coe v23))
                                                                    (coe v24))
                                                                 (coe v13))) in
                                                 coe
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Syntax.C_fork''_484
                                                         v11 v12 v26
                                                         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                            (coe
                                                               du_check'45'complete_2508 (coe v0)
                                                               (coe v16)
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                  (coe v19)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_Many_10)
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
                                                                        du_check'45'complete_2508
                                                                        (coe v0) (coe v16)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                           (coe v19)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C_Many_10)
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
                                                                        du_check'45'complete_2508
                                                                        (coe v0) (coe v16)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                           (coe v19)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C_Many_10)
                                                                              (coe v23))
                                                                           (coe v25))
                                                                        (coe v14)))))
                                                            erased))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_578 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
                             -> case coe v19 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v21 v22
                                    -> let v23
                                             = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    du_check'45'complete_2508 (coe v0) (coe v14)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C__'42'__124
                                                          (coe v15) (coe v18))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe v22))
                                                       (coe v20))
                                                    (coe v12)) in
                                       coe
                                         (let v24
                                                = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                       (coe
                                                          du_check'45'complete_2508 (coe v0)
                                                          (coe v14)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C__'42'__124
                                                                (coe v15) (coe v18))
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                (coe v22))
                                                             (coe v20))
                                                          (coe v12))) in
                                          coe
                                            (let v25
                                                   = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                             (coe
                                                                du_check'45'complete_2508 (coe v0)
                                                                (coe v14)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C__'42'__124
                                                                      (coe v15) (coe v18))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                      (coe v22))
                                                                   (coe v20))
                                                                (coe v12)))) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_curry''_502
                                                     v23)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe addInt (coe (1 :: Integer)) (coe v24))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v25) erased)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_592 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v14 v15 v16
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_130 v17
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                    -> coe
                                         seq (coe v19)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Once.Surface.Syntax.C_cata_516 v10
                                               (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     du_check'45'complete_2508 (coe v0) (coe v13)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                        (coe
                                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                           (coe v17) (coe v16))
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                           (coe v19))
                                                        (coe v16))
                                                     (coe v11))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  addInt (coe (1 :: Integer))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           du_check'45'complete_2508 (coe v0)
                                                           (coe v13)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                                 (coe v17) (coe v16))
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                 (coe v19))
                                                              (coe v16))
                                                           (coe v11)))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              du_check'45'complete_2508 (coe v0)
                                                              (coe v13)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                                    (coe v17) (coe v16))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                    (coe
                                                                       MAlonzo.Code.Once.Type.C_Many_10)
                                                                    (coe v19))
                                                                 (coe v16))
                                                              (coe v11)))))
                                                  erased)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_608 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_132 v18 v19
                             -> let v20
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             du_check'45'complete_2508 (coe v0) (coe v14)
                                             (coe
                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                (coe v15)
                                                (coe
                                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                                (coe
                                                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                   (coe v18) (coe v15)))
                                             (coe v12)) in
                                coe
                                  (let v21
                                         = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   du_check'45'complete_2508 (coe v0) (coe v14)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v15)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v19))
                                                      (coe
                                                         MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                         (coe v18) (coe v15)))
                                                   (coe v12))) in
                                   coe
                                     (let v22
                                            = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         du_check'45'complete_2508 (coe v0)
                                                         (coe v14)
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                            (coe v15)
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                               (coe v19))
                                                            (coe
                                                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                               (coe v18) (coe v15)))
                                                         (coe v12)))) in
                                      coe
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Once.Surface.Syntax.C_ana_532 v11 v20)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe addInt (coe (1 :: Integer)) (coe v21))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v22) erased)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_620 v6 v9 v10
        -> coe du_iFromInferSub_2350 v0 v1 v6 v2 v9 v10
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_640 v10 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Completeness.Rules.du_check'45'complete'45'RLam_1676
                                  (coe v0) (coe v15) (coe v16) (coe v17) (coe v20) (coe v10)
                                  (coe v19)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_656 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v15 v16
                      -> let v17
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_check'45'complete_2508 (coe v0) (coe v13) (coe v15)
                                      (coe v11)) in
                         coe
                           (let v18
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_check'45'complete_2508 (coe v0) (coe v13) (coe v15)
                                            (coe v11))) in
                            coe
                              (coe
                                 du_pair'45'lit'45'reduce_2408 (coe v9) (coe v10) (coe v17)
                                 (coe v18)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       du_check'45'complete_2508 (coe v0) (coe v14) (coe v16)
                                       (coe v12)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          du_check'45'complete_2508 (coe v0) (coe v14) (coe v16)
                                          (coe v12))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             du_check'45'complete_2508 (coe v0) (coe v14) (coe v16)
                                             (coe v12)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_666 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v12
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'In_2970
                           (coe v0) (coe v11) (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_678 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply_3134
                    (coe v0) (coe v2) (coe v11) (coe v6) (coe v2) (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          du_infer'45'complete_2440 (coe v0) (coe v11)
                          (coe
                             MAlonzo.Code.Once.Type.C__'42'__124
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v6)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                (coe v2))
                             (coe v6))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             du_infer'45'complete_2440 (coe v0) (coe v11)
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe
                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v6)
                                   (coe
                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                      (coe MAlonzo.Code.Once.Type.C_pure_34))
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
                                du_infer'45'complete_2440 (coe v0) (coe v11)
                                (coe
                                   MAlonzo.Code.Once.Type.C__'42'__124
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v6)
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                                      (coe v2))
                                   (coe v6))
                                (coe v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_690 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v12 v13
                      -> coe
                           du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2132 (coe v0)
                           (coe v11) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_702 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v12 v13
                      -> coe
                           du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2180 (coe v0)
                           (coe v11) (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_712 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2226
                    (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_726 v7 v8 v9 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'poly_4786
                    (coe v0) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
