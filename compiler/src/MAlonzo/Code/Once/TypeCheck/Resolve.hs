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

module MAlonzo.Code.Once.TypeCheck.Resolve where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Resolve.CtxMatch
d_CtxMatch_8 a0 a1 a2 = ()
data T_CtxMatch_8
  = C_match'45'empty_10 | C_match'45'extend_24 T_CtxMatch_8
-- Once.TypeCheck.Resolve.lookupNamedIdx
d_lookupNamedIdx_26 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupNamedIdx_26 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_22 (coe v2))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe
                              seq (coe v6)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                    (coe MAlonzo.Code.Once.TypeCheck.Context.d_type_24 (coe v2))))
                       else coe
                              seq (coe v6)
                              (let v7 = d_lookupNamedIdx_26 (coe v0) (coe v3) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe addInt (coe (1 :: Integer)) (coe v9))
                                                     (coe v10))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Resolve.natToFin
d_natToFin_76 ::
  Integer -> Integer -> Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_natToFin_76 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (let v4 = d_natToFin_76 (coe v3) (coe v2) in
                        coe
                          (case coe v4 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v5)
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                             _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.TypeCheck.Resolve._≟T_
d__'8799'T__98 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> Bool
d__'8799'T__98 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_6
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Unit_6
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Void_8
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Void_8
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__'42'__10 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__10 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d__'8799'T__98 (coe v3) (coe v5))
                       (coe d__'8799'T__98 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__'43'__12 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__12 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d__'8799'T__98 (coe v3) (coe v5))
                       (coe d__'8799'T__98 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__'8658'__14 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658'__14 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d__'8799'T__98 (coe v3) (coe v5))
                       (coe d__'8799'T__98 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Eff_16 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Eff_16 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d__'8799'T__98 (coe v3) (coe v5))
                       (coe d__'8799'T__98 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Fix_18 v3
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Fix_18 v4
                  -> coe d__'8799'T__98 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Int_20
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Int_20
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Float_22
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Float_22
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Str_24
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Str_24
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Buffer_26
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Buffer_26
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_TVar_28 v3
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_TVar_28 v4
                  -> let v5
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v5 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v3))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v3)
                                  (coe v4)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                            -> if coe v6
                                 then coe seq (coe v7) (coe v6)
                                 else coe seq (coe v7) (coe v6)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Resolve.resolve
d_resolve_162 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_CtxMatch_8 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  Maybe MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_resolve_162 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v6
        -> let v7 = d_lookupNamedIdx_26 (coe v6) (coe v1) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                  -> case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> let v11 = d_natToFin_76 (coe v9) (coe v0) in
                            coe
                              (let v12 = d__'8799'T__98 (coe v5) (coe v10) in
                               coe
                                 (case coe v11 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                      -> if coe v12
                                           then coe
                                                  d_postulate'45'var_276 v9 v10 v0 v5 v13 v1 v6 v2
                                                  v3 v0 v1 v2 v3 v6 v5 v13
                                           else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v11
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_38 v6 v7
        -> coe
             d_postulate'45'app_348 v0 v1 v2 v3 v6 v7 v5 v0 v1 v2 v3 v6 v7 v5
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_40 v6 v7
        -> let v8 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v5 of
                MAlonzo.Code.Once.Type.C__'8658'__14 v9 v10
                  -> let v11
                           = d_resolve_162
                               (coe addInt (coe (1 :: Integer)) (coe v0))
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__34 (coe v1)
                                  (coe v6) (coe v9))
                               (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v2 v9)
                               (coe C_match'45'extend_24 v3) (coe v7) (coe v10) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v12)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v11
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v8)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_42 v6 v7 v8
        -> coe
             d_postulate'45'let_462 v0 v1 v2 v3 v6 v7 v8 v5 v0 v1 v2 v3 v6 v7 v8
             v5
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_44 v6 v7
        -> let v8 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v5 of
                MAlonzo.Code.Once.Type.C__'42'__10 v9 v10
                  -> let v11
                           = d_resolve_162
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v9) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                            -> let v13
                                     = d_resolve_162
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v10) in
                               coe
                                 (case coe v13 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v12 v14)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v13
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v11
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v8)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RCase_46 v6 v7 v8 v9 v10
        -> coe
             d_postulate'45'case_492 v0 v1 v2 v3 v6 v7 v8 v9 v10 v5 v0 v1 v2 v3
             v6 v7 v8 v9 v10 v5
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_48
        -> let v6 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v5 of
                MAlonzo.Code.Once.Type.C_Unit_6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124)
                _ -> coe v6)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_50 v6
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_52 v6
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_54 v6 v7
        -> coe
             d_resolve_162 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_56 v6 v7 v8
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_58 v7
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Resolve._.postulate-var
d_postulate'45'var_276
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Resolve._.postulate-var"
-- Once.TypeCheck.Resolve._.postulate-app
d_postulate'45'app_348
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Resolve._.postulate-app"
-- Once.TypeCheck.Resolve._.postulate-let
d_postulate'45'let_462
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Resolve._.postulate-let"
-- Once.TypeCheck.Resolve._.postulate-case
d_postulate'45'case_492
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Resolve._.postulate-case"
-- Once.TypeCheck.Resolve.resolveClosed
d_resolveClosed_508 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  Maybe MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_resolveClosed_508 v0 v1
  = coe
      d_resolve_162 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_32)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe C_match'45'empty_10) (coe v0) (coe v1)
-- Once.TypeCheck.Resolve.resolve-well-typed
d_resolve'45'well'45'typed_528 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_CtxMatch_8 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_resolve'45'well'45'typed_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_resolve'45'well'45'typed_528 v6
du_resolve'45'well'45'typed_528 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
du_resolve'45'well'45'typed_528 v0 = coe v0
